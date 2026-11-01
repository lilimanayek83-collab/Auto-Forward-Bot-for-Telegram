#!/usr/bin/env python3
"""
Telegram Auto-Forwarder  v8.0   (bot + userbot, Telethon + MongoDB)
====================================================================
Run:    python3 forward_bot.py
Setup:  everything is done from the bot's private chat (/start).

Concepts
--------
A *batch* = N sources  ->  M targets  +  its own rules.
  * many sources -> one target   : put several sources + one target in a batch
  * one source  -> many targets  : put one source + several targets in a batch
  * rules per batch: include keywords, exclude keywords, "if both match" policy,
    optional member filter, pause/resume.

Filter logic (per batch)
------------------------
  include set / exclude set / message matches      -> result
  none / none                                      -> forward
  include only   : matches an include keyword      -> forward, else skip
  exclude only   : matches an exclude keyword      -> skip,    else forward
  both configured:
      include hit, exclude miss -> forward
      include miss (any)        -> skip
      include hit, exclude hit  -> "conflict policy" chosen by you: SEND or DON'T SEND
Keywords are case-insensitive substrings; prefix with  re:  for a regex.
They are searched in: message text/caption, file name, and button labels.

Who captures what
-----------------
  * Bot account  : captures everything it can see (channels where it is admin,
                   groups where it is admin or privacy mode is OFF).
  * Userbot      : (logged in + switched ON) captures
                     - messages written by OTHER BOTS (Telegram never shows them to a bot)
                     - everything from sources the bot account cannot see at all.
  A message is always sent by the same account that captured it
  (Telegram file references are bound to the session that fetched them), so the
  userbot must be a member/admin of the targets that receive its captures.

What changed vs v7.6 (bugs fixed)
---------------------------------
  * Duplicates: a message is now delivered AT MOST ONCE per target (checked against
    MongoDB), even if two batches overlap, both accounts see it, you restart,
    or Telegram replays updates.  Edit-sync no longer deletes + re-sends.
  * Lost messages: FloodWait used to drop the message - now it waits and retries.
    Long captions (>1024) are split instead of failing. Callback/inline buttons that
    caused send errors are converted (URL buttons kept; userbot gets them as links).
    Expired file references fall back to download + re-upload. Entity errors retry
    as plain text. Failures are reported to the admin instead of vanishing.
  * Order: every source has its own queue, so messages arrive in the same order.
  * Albums are forwarded as albums (and edit/delete-synced per item).
  * Loop protection: copies made by this bot are never forwarded again.
  * Privacy-mode / not-admin groups are detected -> userbot takes over automatically.
  * Login: Telegram invalidates login codes typed in plain text inside Telegram.
    Send the code with separators (1-2-3-4-5); the bot strips them.
"""
from __future__ import annotations

import asyncio
import functools
import hashlib
import html
import logging
import os
import re
import shutil
import tempfile
import time
from collections import Counter, OrderedDict
from datetime import datetime, timezone
from typing import Dict, List, Optional, Tuple

import motor.motor_asyncio
from dotenv import load_dotenv
from pymongo import ReturnDocument
from telethon import TelegramClient, events, utils
from telethon.errors import (
    FloodWaitError, InviteHashExpiredError, InviteHashInvalidError,
    MessageNotModifiedError, PasswordHashInvalidError, PhoneCodeExpiredError,
    PhoneCodeInvalidError, PhoneNumberInvalidError, SessionPasswordNeededError,
    UserAlreadyParticipantError,
)
from telethon.tl.custom import Button
from telethon.tl.functions.messages import CheckChatInviteRequest, ImportChatInviteRequest
from telethon.tl.types import (
    ChatInviteAlready, ChatInvitePeek, MessageMediaEmpty, MessageMediaWebPage,
    MessageService, PeerUser, UpdateDeleteChannelMessages, User,
)

# ════════════════════════════════ CONFIG ════════════════════════════════
load_dotenv()


def _env(key: str, required: bool = True, default: str = "") -> str:
    val = os.environ.get(key, default).strip().strip('"').strip("'")
    if not val and required:
        raise RuntimeError(f"Missing .env key: {key}")
    return val


BOT_TOKEN = _env("BOT_TOKEN")
API_ID = int(_env("API_ID"))
API_HASH = _env("API_HASH")
MONGO_URL = _env("MONGO_URL")
MONGO_DB = _env("MONGO_DB", False, "forwarder")
ADMIN_IDS = [int(x) for x in re.findall(r"-?\d+", _env("ADMIN"))]

KEEPALIVE = int(_env("KEEPALIVE", False, "300"))            # seconds between health checks
MAP_TTL_DAYS = int(_env("MAP_TTL_DAYS", False, "30"))       # how long edit/delete-sync mapping is kept
SYNC_EDITS = _env("SYNC_EDITS", False, "1") != "0"
SYNC_DELETES = _env("SYNC_DELETES", False, "1") != "0"
CATCH_UP = _env("CATCH_UP", False, "1") != "0"              # replay updates missed while offline
MAX_REUPLOAD_MB = int(_env("MAX_REUPLOAD_MB", False, "1500"))
SEND_DELAY = float(_env("SEND_DELAY", False, "0.4"))        # pause between sends (anti-flood)

MAP_CACHE_SIZE = 20000
DEVICE_MODEL, SYS_VER, APP_VER = "Samsung Galaxy S21 Ultra", "Android 13", "9.6.1 (3882)"

logging.basicConfig(format="%(asctime)s │ %(levelname)-7s │ %(message)s", level=logging.INFO)
log = logging.getLogger("forwarder")
logging.getLogger("telethon").setLevel(logging.WARNING)

# ════════════════════════════════ STATE ═════════════════════════════════


class State:
    user_client: Optional[TelegramClient] = None
    authorized = False          # userbot session is really logged in
    enabled = False             # user-controlled ON/OFF switch (persisted)
    premium = False
    handlers_ready = False      # capture handlers bound to the CURRENT user_client
    runner: Optional[asyncio.Task] = None
    bot_me = None


S = State()
batches: Dict[int, dict] = {}           # batch_id -> batch document
bot_access: Dict[int, bool] = {}        # source_id -> can the BOT account actually receive its messages?
sessions: Dict[int, dict] = {}          # admin id -> pending text-input step
login_sessions: Dict[int, dict] = {}
STATS: Counter = Counter()

_bg_tasks: set = set()


def _spawn(coro) -> asyncio.Task:
    """create_task() that keeps a strong reference (asyncio only keeps weak ones)."""
    t = asyncio.create_task(coro)
    _bg_tasks.add(t)
    t.add_done_callback(_bg_tasks.discard)
    return t


def new_user_client() -> TelegramClient:
    # A logged-out Telethon client can't be reused, so logout always builds a fresh one.
    return TelegramClient("forwarder_user_session", API_ID, API_HASH, device_model=DEVICE_MODEL,
                          system_version=SYS_VER, app_version=APP_VER, flood_sleep_threshold=60)


bot_client = TelegramClient("forwarder_bot_session", API_ID, API_HASH, flood_sleep_threshold=60)
bot_client.parse_mode = "html"          # UI messages use HTML; copies pass their own parse_mode
S.user_client = new_user_client()

# ════════════════════════════════ DATABASE ══════════════════════════════
_mongo = motor.motor_asyncio.AsyncIOMotorClient(MONGO_URL)
_db = _mongo[MONGO_DB]
col_batches, col_msgmap, col_meta = _db["batches"], _db["message_map"], _db["meta"]

MapEntry = Tuple[int, int, str, bool]   # (target_chat_id, target_msg_id, via 'bot'|'user', is_extra)
_map_cache: "OrderedDict[Tuple[int, int], List[MapEntry]]" = OrderedDict()


async def db_init():
    try:
        await col_msgmap.create_index("created_at", expireAfterSeconds=MAP_TTL_DAYS * 86400, name="ttl_created")
    except Exception as e:  # e.g. an index with other options already exists
        log.warning(f"TTL index not created: {e}")


async def db_next_id() -> int:
    r = await col_meta.find_one_and_update({"_id": "batch_counter"}, {"$inc": {"value": 1}},
                                           upsert=True, return_document=ReturnDocument.AFTER)
    return r["value"]


async def db_save_batch(bid: int, b: dict):
    await col_batches.replace_one({"_id": bid}, {"_id": bid, **b}, upsert=True)


async def db_load_userbot_enabled() -> bool:
    doc = await col_meta.find_one({"_id": "userbot_state"})
    return bool(doc and doc.get("enabled"))


async def db_save_userbot_enabled(val: bool):
    await col_meta.update_one({"_id": "userbot_state"}, {"$set": {"enabled": bool(val)}}, upsert=True)


def _cache_put(key, entries):
    _map_cache[key] = entries
    _map_cache.move_to_end(key)
    while len(_map_cache) > MAP_CACHE_SIZE:
        _map_cache.popitem(last=False)


async def map_get(sc: int, sm: int) -> List[MapEntry]:
    """Where was source message (sc, sm) copied to?  MongoDB is the source of truth."""
    key = (sc, sm)
    if key in _map_cache:
        return list(_map_cache[key])
    doc = await col_msgmap.find_one({"_id": f"{sc}:{sm}"})
    entries = [(t["chat_id"], t["msg_id"], t.get("via", "bot"), bool(t.get("extra", False)))
               for t in doc["targets"]] if doc else []
    _cache_put(key, entries)
    return list(entries)


async def map_set(sc: int, sm: int, entries: List[MapEntry]):
    _cache_put((sc, sm), list(entries))
    _id = f"{sc}:{sm}"
    if entries:
        await col_msgmap.replace_one({"_id": _id}, {
            "_id": _id, "source_chat_id": sc, "source_msg_id": sm,
            "created_at": datetime.now(timezone.utc),
            "targets": [{"chat_id": c, "msg_id": m, "via": v, "extra": x} for c, m, v, x in entries],
        }, upsert=True)
    else:
        await col_msgmap.delete_one({"_id": _id})


async def map_pop(sc: int, sm: int) -> List[MapEntry]:
    entries = await map_get(sc, sm)
    _map_cache.pop((sc, sm), None)
    await col_msgmap.delete_one({"_id": f"{sc}:{sm}"})
    return entries


# ════════════════════════════════ BATCH MODEL ═══════════════════════════
def canonical_id(raw) -> int:
    raw = int(raw)
    return raw if raw < 0 else int(f"-100{raw}")


def same_chat(a, b) -> bool:
    return canonical_id(a) == canonical_id(b)


def normalize_batch(b: dict) -> dict:
    """Fill defaults and upgrade v7.x documents (single source_id) to the multi-source layout."""
    if "sources" not in b:
        b["sources"] = ([{"id": b["source_id"], "name": b.get("source_name", str(b["source_id"]))}]
                        if "source_id" in b else [])
    for old in ("source_id", "source_name", "bot_has_access"):
        b.pop(old, None)
    b.setdefault("targets", [])
    b.setdefault("target_members", [])
    b.setdefault("filter_keywords", [])      # include keywords (same name as v7 for compatibility)
    b.setdefault("exclude_keywords", [])
    b.setdefault("conflict_policy", "skip")  # when a message matches include AND exclude: 'send' | 'skip'
    b.setdefault("enabled", True)
    return b


def new_batch() -> dict:
    return normalize_batch({})


def batches_for_source(sid: int) -> List[dict]:
    return [b for b in batches.values() if any(s["id"] == sid for s in b["sources"])]


def all_sources() -> Dict[int, str]:
    return {s["id"]: s["name"] for b in batches.values() for s in b["sources"]}


# ════════════════════════════════ FILTERS ═══════════════════════════════
def kw_hit(keywords: List[str], text: str) -> Optional[str]:
    """First keyword found in text (case-insensitive). 're:<pattern>' = regex."""
    low = text.casefold()
    for kw in keywords:
        if kw[:3].lower() == "re:":
            try:
                if re.search(kw[3:], text, re.I | re.S):
                    return kw
            except re.error:
                continue
        elif kw.casefold() in low:
            return kw
    return None


def evaluate_filters(batch: dict, text: str, sender_id: Optional[int]) -> Tuple[bool, str]:
    members = batch["target_members"]
    if members and sender_id not in {m["id"] for m in members}:
        return False, "sender not in member filter"
    inc, exc = batch["filter_keywords"], batch["exclude_keywords"]
    inc_hit = kw_hit(inc, text) if inc else None
    exc_hit = kw_hit(exc, text) if exc else None
    if inc and exc:
        if inc_hit and exc_hit:
            send = batch["conflict_policy"] == "send"
            return send, f"matches include '{inc_hit}' AND exclude '{exc_hit}' -> policy {'SEND' if send else 'SKIP'}"
        if inc_hit:
            return True, f"matches include '{inc_hit}'"
        return False, "no include keyword matched"
    if inc:
        return (True, f"matches include '{inc_hit}'") if inc_hit else (False, "no include keyword matched")
    if exc:
        return (False, f"matches exclude '{exc_hit}'") if exc_hit else (True, "no exclude keyword matched")
    return True, "no keyword filter"


def url_rows(msg) -> List[List[Tuple[str, str]]]:
    """URL buttons of a message as [[(label, url), ...], ...]. Callback / switch-inline buttons are
    dropped (they'd be dead copies). Duck-typed so it works across Telethon versions."""
    rows = []
    for row in (getattr(msg.reply_markup, "rows", None) or []):
        cur = [(b.text, b.url) for b in row.buttons if getattr(b, "url", None) and getattr(b, "text", None)]
        if cur:
            rows.append(cur)
    return rows


def searchable_text(msgs) -> str:
    parts = []
    for m in msgs:
        if m.message:
            parts.append(m.message)
        if m.file is not None and m.file.name:
            parts.append(m.file.name)
        parts.extend(label for row in url_rows(m) for label, _ in row)
    return "\n".join(parts)


def group_albums(msgs: list) -> List[list]:
    groups, cur, gid = [], [], None
    for m in msgs:
        g = m.grouped_id
        if g and g == gid:
            cur.append(m)
        else:
            if cur:
                groups.append(cur)
            cur, gid = [m], g
    if cur:
        groups.append(cur)
    return groups


# ════════════════════════════ ORDERED PER-SOURCE QUEUES ═════════════════
# Every operation on a source (new message, edit, delete, bulk) runs through one queue,
# so order is preserved and "check-then-send" duplicate checks can't race each other.
_queues: Dict[int, asyncio.Queue] = {}


async def _worker(sid: int, q: asyncio.Queue):
    while True:
        fn, fut = await q.get()
        try:
            res = await fn()
            if fut and not fut.done():
                fut.set_result(res)
        except Exception as e:
            log.exception(f"job failed for source {sid}")
            if fut and not fut.done():
                fut.set_exception(e)
        finally:
            q.task_done()


def _queue_for(sid: int) -> asyncio.Queue:
    q = _queues.get(sid)
    if q is None:
        q = _queues[sid] = asyncio.Queue()
        _spawn(_worker(sid, q))
    return q


def enqueue(sid: int, fn):
    _queue_for(sid).put_nowait((fn, None))


async def run_serial(sid: int, fn):
    fut = asyncio.get_running_loop().create_future()
    _queue_for(sid).put_nowait((fn, fut))
    return await fut


# ════════════════════════════ LOOP PROTECTION / ALERTS ══════════════════
_sent_ids: "OrderedDict[Tuple[int, int], None]" = OrderedDict()
_last_alert: Dict[str, float] = {}


def remember_sent(chat_id: int, msg_id: int):
    _sent_ids[(canonical_id(chat_id), msg_id)] = None
    while len(_sent_ids) > 50000:
        _sent_ids.popitem(last=False)


def is_own_copy(chat_id: int, msg_id: int) -> bool:
    return (canonical_id(chat_id), msg_id) in _sent_ids


async def alert(key: str, text: str):
    """Tell the first admin about a problem (max once per 10 min per key)."""
    now = time.time()
    if now - _last_alert.get(key, 0) < 600:
        return
    _last_alert[key] = now
    try:
        await bot_client.send_message(ADMIN_IDS[0], text, link_preview=False)
    except Exception:
        pass


# ════════════════════════════ COPYING MESSAGES ══════════════════════════
class _Raw:
    """parse_mode shim: hand Telethon the exact entities (bold, links, spoilers...) we already have.
    Going through parse_mode (instead of formatting_entities) also makes it work for albums and
    lets Telethon drop mention entities it can't resolve instead of failing the whole send."""

    def __init__(self, entities):
        self.entities = entities

    def parse(self, text):
        return text, list(self.entities)

    def unparse(self, text, entities):
        return text


def u16len(s: str) -> int:
    return len(s.encode("utf-16-le")) // 2


def has_media(m) -> bool:
    return bool(m.media) and not isinstance(m.media, (MessageMediaWebPage, MessageMediaEmpty))


def err_code(e: Exception) -> str:
    return str(getattr(e, "message", "") or type(e).__name__).upper()


def caption_limit(client) -> int:
    return 2048 if (client is not bot_client and S.premium) else 1024


def build_payload(msg, via: str, album: bool = False):
    """(text, entities, buttons). URL buttons stay buttons for the bot account; a user account
    can't send inline keyboards, so for it they're appended as '🔗 label: url' lines."""
    text = msg.message or ""
    entities = list(msg.entities or [])
    rows = url_rows(msg)
    markup = None
    if rows:
        if via == "bot" and not album:
            markup = [[Button.url(t, u) for t, u in row] for row in rows]
        else:
            lines = "\n".join(f"🔗 {t}: {u}" for row in rows for t, u in row)
            text = f"{text}\n\n{lines}" if text else lines
    return text, entities, markup


async def _do_send(client, target_id, msgs, text, entities, markup, files=None, **kw):
    """One send attempt. Returns [(sent_msg_id, is_extra)]."""
    pm = _Raw(entities)
    media = files if files is not None else [m.media for m in msgs if has_media(m)]
    out: List[Tuple[int, bool]] = []
    if media:
        split = u16len(text) > caption_limit(client)       # caption too long -> media first, text after
        single = len(media) == 1
        sent = await client.send_file(
            target_id, media[0] if single else media,
            caption="" if split else text, parse_mode=None if split else pm,
            buttons=markup if (single and not split) else None, **kw)
        for s in (sent if isinstance(sent, list) else [sent]):
            remember_sent(target_id, s.id)
            out.append((s.id, False))
        if split:
            s = await client.send_message(target_id, text, parse_mode=pm, buttons=markup, link_preview=False)
            remember_sent(target_id, s.id)
            out.append((s.id, True))
    else:
        s = await client.send_message(
            target_id, text, parse_mode=pm, buttons=markup,
            link_preview=any(isinstance(m.media, MessageMediaWebPage) for m in msgs))
        remember_sent(target_id, s.id)
        out.append((s.id, False))
    return out


async def _send_reupload(client, msgs, target_id, text, entities, markup):
    """Fallback when Telegram rejects the file reference: download, then upload again."""
    total = sum((m.file.size or 0) for m in msgs if m.file is not None)
    if total > MAX_REUPLOAD_MB * 1024 * 1024:
        raise RuntimeError(f"file too large to re-upload ({total // 2**20} MB)")
    tmp = tempfile.mkdtemp(prefix="fwd_")
    try:
        paths = []
        for m in msgs:
            if not has_media(m):
                continue
            d = os.path.join(tmp, str(m.id))
            os.makedirs(d)
            p = await m.download_media(file=d + os.sep)
            if not p:
                raise RuntimeError("download failed")
            paths.append(p)
        kw = {}
        if len(paths) == 1 and msgs[0].document is not None:
            kw = {"attributes": msgs[0].document.attributes, "supports_streaming": True}
        return await _do_send(client, target_id, msgs, text, entities, markup, files=paths, **kw)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


async def send_copy(client, msgs, target_id, via) -> List[Tuple[int, bool]]:
    caption_msg = next((m for m in msgs if m.message), msgs[0])
    text, entities, markup = build_payload(caption_msg, via, album=len(msgs) > 1)
    media_present = any(has_media(m) for m in msgs)
    if not text and not media_present:
        return []
    plain = False
    for _ in range(4):
        ents = [] if plain else entities
        try:
            return await _do_send(client, target_id, msgs, text, ents, markup)
        except FloodWaitError as e:
            log.warning(f"FloodWait {e.seconds}s while sending to {target_id}; waiting then retrying")
            await asyncio.sleep(e.seconds + 2)
        except Exception as e:
            code = err_code(e)
            if "ENTIT" in code and not plain:
                plain = True
                continue
            if media_present and any(k in code for k in ("FILE_REFERENCE", "MEDIA_EMPTY", "MEDIA_INVALID")):
                log.info(f"{code}: falling back to download + re-upload")
                return await _send_reupload(client, msgs, target_id, text, ents, markup)
            raise
    raise RuntimeError("gave up after repeated FloodWait")


async def deliver(msgs: list, source_id: int, client, only_batch: Optional[dict] = None) -> Tuple[int, int]:
    """Apply every matching batch's rules to one message (or album) and copy it to the union of
    allowed targets - never twice to the same target. Returns (copies_sent, failures)."""
    msgs = [m for m in msgs if m is not None and not isinstance(m, MessageService)]
    if not msgs:
        return 0, 0
    first = msgs[0]
    if is_own_copy(source_id, first.id):
        return 0, 0
    via = "bot" if client is bot_client else "user"
    text = searchable_text(msgs)
    targets: "OrderedDict[int, str]" = OrderedDict()
    for b in ([only_batch] if only_batch else batches_for_source(source_id)):
        if not b["enabled"]:
            continue
        ok, why = evaluate_filters(b, text, first.sender_id)
        if ok:
            for t in b["targets"]:
                targets.setdefault(t["id"], t["name"])
        else:
            STATS["filtered"] += 1
            log.info(f"⛔ msg {first.id} skipped ({why})")
    if not targets:
        return 0, 0

    sc = canonical_id(source_id)
    already = {e[0] for e in await map_get(sc, first.id)}
    added: Dict[int, List[MapEntry]] = {m.id: [] for m in msgs}
    sent_n = failed_n = 0
    for tid, tname in targets.items():
        if tid in already:
            continue
        try:
            sent = await send_copy(client, msgs, tid, via)
        except Exception as e:
            failed_n += 1
            STATS["errors"] += 1
            log.error(f"❌ msg {first.id} -> '{tname}': {type(e).__name__}: {e}")
            await alert(f"send:{tid}", f"⚠️ Could not forward to <b>{html.escape(tname)}</b>\n"
                                       f"<code>{html.escape(type(e).__name__)}: {html.escape(str(e))[:300]}</code>\n"
                                       f"Check that the {'bot' if via == 'bot' else 'userbot'} account is an admin "
                                       f"(with post permission) there.")
            continue
        if not sent:
            continue
        sent_n += 1
        STATS["forwarded"] += 1
        regular = [sid for sid, extra in sent if not extra]
        for m, sid in zip(msgs, regular):
            added[m.id].append((tid, sid, via, False))
        for sid, extra in sent:
            if extra:
                added[first.id].append((tid, sid, via, True))
        log.info(f"✉️  msg {first.id}{' (+album)' if len(msgs) > 1 else ''} -> '{tname}' via {via}")
        await asyncio.sleep(SEND_DELAY)
    for m in msgs:
        if added[m.id]:
            await map_set(sc, m.id, await map_get(sc, m.id) + added[m.id])
    return sent_n, failed_n


# ════════════════════════════ EDIT / DELETE SYNC ════════════════════════
_edit_seen: "OrderedDict[Tuple[int, int], str]" = OrderedDict()


def _clients_for(via: str):
    pref = [bot_client, S.user_client] if via == "bot" else [S.user_client, bot_client]
    return [c for c in pref if c is not None and (c is bot_client or S.authorized)]


async def apply_edit(msg, source_id: int, client):
    sc = canonical_id(source_id)
    entries = await map_get(sc, msg.id)
    if not entries:
        return
    sig = hashlib.sha1(f"{msg.message}|{msg.entities}|{msg.reply_markup}".encode()).hexdigest()
    if _edit_seen.get((sc, msg.id)) == sig:        # reactions/views also trigger "edited" updates
        return
    for tid, tmid, via, extra in entries:
        if extra:
            continue                               # split-caption text part: not editable in place
        text, entities, markup = build_payload(msg, via)
        editor = _clients_for(via)[0]
        for attempt in range(2):
            try:
                await editor.edit_message(tid, tmid, text=text, parse_mode=_Raw(entities), buttons=markup,
                                          link_preview=isinstance(msg.media, MessageMediaWebPage))
                log.info(f"✏️  edit-synced {msg.id} -> {tid}:{tmid}")
                break
            except MessageNotModifiedError:
                break
            except FloodWaitError as e:
                await asyncio.sleep(e.seconds + 1)
            except Exception as e:
                log.warning(f"edit-sync {tid}:{tmid} failed: {e}")
                break
    _edit_seen[(sc, msg.id)] = sig
    while len(_edit_seen) > 5000:
        _edit_seen.popitem(last=False)


async def delete_sync(sc: int, ids: List[int]):
    for mid in ids:
        for tid, tmid, via, _ in await map_pop(sc, mid):
            for c in _clients_for(via):
                try:
                    await c.delete_messages(tid, [tmid])
                    STATS["deleted"] += 1
                    log.info(f"🗑  delete-synced {mid} -> {tid}:{tmid}")
                    break
                except FloodWaitError as e:
                    await asyncio.sleep(e.seconds + 1)
                except Exception as e:
                    log.debug(f"delete {tid}:{tmid} via {type(c).__name__}: {e}")


# ════════════════════════════ LIVE CAPTURE ══════════════════════════════
async def _is_bot_sender(msg) -> bool:
    try:
        sender = await msg.get_sender()
        return bool(getattr(sender, "bot", False))
    except Exception:
        return False


def register_capture(client, kind: str):
    """Bind live handlers to a client. kind='bot': handles whatever the bot receives.
    kind='user': only acts while the userbot switch is ON, and only for bot-authored messages
    (or everything, for sources the bot account can't see)."""

    def schedule(chat_id, msgs, edited=False):
        if chat_id is None:
            return
        sid = canonical_id(chat_id)
        if not batches_for_source(sid):
            return

        async def job():
            if kind == "user":
                if not S.enabled:
                    return
                if bot_access.get(sid, True) and not await _is_bot_sender(msgs[0]):
                    return                      # the bot account handles human senders itself
            if msgs[0].out:                     # our own account's message: give remember_sent() time
                await asyncio.sleep(1.0)
            if edited:
                if SYNC_EDITS:
                    await apply_edit(msgs[0], sid, client)
            else:
                await deliver(msgs, sid, client)

        enqueue(sid, job)

    @client.on(events.NewMessage(func=lambda e: not e.is_private))
    async def _new(event):
        if event.message.grouped_id:            # album items are handled together by the Album event
            return
        schedule(event.chat_id, [event.message])

    @client.on(events.Album(func=lambda e: not e.is_private))
    async def _album(event):
        schedule(event.chat_id, list(event.messages))

    @client.on(events.MessageEdited(func=lambda e: not e.is_private))
    async def _edit(event):
        schedule(event.chat_id, [event.message], edited=True)

    if SYNC_DELETES:
        @client.on(events.Raw(UpdateDeleteChannelMessages))
        async def _delete(update):
            sc = canonical_id(update.channel_id)
            if not batches_for_source(sc):
                return
            ids = list(update.messages)

            async def job():
                if kind == "user" and not S.enabled:
                    return
                await delete_sync(sc, ids)
            enqueue(sc, job)


register_capture(bot_client, "bot")


# ════════════════════════════ ACCESS / USERBOT LIFECYCLE ════════════════
async def check_bot_access(sid: int) -> bool:
    """Will the BOT account actually receive live messages from this chat?"""
    try:
        ent = await bot_client.get_entity(sid)
        await bot_client.get_messages(ent, limit=1)
        if getattr(ent, "broadcast", False):
            return True                                         # a bot can only be in a channel as admin
        if getattr(S.bot_me, "bot_chat_history", False):
            return True                                         # privacy mode OFF: sees all group messages
        perms = await bot_client.get_permissions(ent, S.bot_me)
        return bool(perms.is_admin)                             # admins always see everything
    except Exception as e:
        log.warning(f"bot has no usable access to {sid}: {e}")
        return False


async def refresh_access():
    for sid in list(all_sources()):
        ok = await check_bot_access(sid)
        if bot_access.get(sid) != ok:
            log.info(f"source {sid}: bot access = {ok}")
        bot_access[sid] = ok
        await asyncio.sleep(0.3)


async def warm_userbot():
    if not (S.authorized and S.enabled):
        return
    for sid in list(all_sources()):
        try:
            await S.user_client.get_messages(sid, limit=1)
        except Exception as e:
            log.debug(f"userbot cannot read {sid}: {e}")
        await asyncio.sleep(0.3)


async def keepalive_loop():
    while True:
        await asyncio.sleep(KEEPALIVE)
        try:
            await refresh_access()
            await warm_userbot()
        except Exception:
            log.exception("keepalive")


async def activate_userbot():
    """Run once the user session is really authorized (startup or fresh login)."""
    if not S.handlers_ready:
        register_capture(S.user_client, "user")
        S.handlers_ready = True
    try:
        S.premium = bool(getattr((await S.user_client.get_me()), "premium", False))
        await S.user_client.get_dialogs()           # fills the entity cache so -100… ids resolve
    except Exception as e:
        log.warning(f"userbot warm-up: {e}")
    if CATCH_UP:
        try:
            await S.user_client.catch_up()
        except Exception as e:
            log.debug(f"userbot catch_up: {e}")
    if S.runner is None or S.runner.done():
        S.runner = _spawn(S.user_client.run_until_disconnected())


# ════════════════════════════ UI HELPERS ════════════════════════════════
def esc(x) -> str:
    return html.escape(str(x), quote=False)


def admin_only(fn):
    @functools.wraps(fn)
    async def wrapper(event):
        if event.sender_id not in ADMIN_IDS:
            return
        return await fn(event)
    return wrapper


async def say(event, text, buttons=None):
    """Edit in place for button presses, new message otherwise."""
    if isinstance(event, events.CallbackQuery.Event):
        try:
            await event.edit(text, buttons=buttons, link_preview=False)
            return
        except MessageNotModifiedError:
            return
        except Exception:
            pass
    await event.respond(text, buttons=buttons, link_preview=False)


def main_menu():
    rows = [[Button.inline("📦 New Batch", "m:new"), Button.inline("📋 My Batches", "m:list")],
            [Button.inline("📊 Status", "m:status"), Button.inline("❓ Help", "m:help")]]
    if not S.authorized:
        rows.append([Button.inline("🔐 Userbot Login", "m:ub_login")])
    else:
        rows.append([Button.inline("🟢 Userbot ON (tap = OFF)" if S.enabled else "⚪ Userbot OFF (tap = ON)", "m:ub_toggle"),
                     Button.inline("🚪 Logout", "m:ub_logout")])
    return rows


FIELDS = {
    "src": {"key": "sources", "kind": "chat", "title": "📡 Sources",
            "prompt": "Send the <b>source</b> chat: forward a message from it, or send its @username, "
                      "invite link, <code>t.me/c/…</code> link or numeric ID."},
    "tgt": {"key": "targets", "kind": "chat", "title": "🎯 Targets",
            "prompt": "Send the <b>target</b> chat: forward a message from it, or send its @username, "
                      "invite link, <code>t.me/c/…</code> link or numeric ID."},
    "mem": {"key": "target_members", "kind": "member", "title": "👤 Member filter",
            "prompt": "Send a member's numeric ID, @username, or forward a message from them. "
                      "Only these senders will be forwarded (leave empty = everyone)."},
    "inc": {"key": "filter_keywords", "kind": "kw", "title": "✅ Include keywords",
            "prompt": "Send keywords — <b>one per line</b>. Only messages containing one of them are forwarded. "
                      "Prefix with <code>re:</code> for a regex."},
    "exc": {"key": "exclude_keywords", "kind": "kw", "title": "🚫 Exclude keywords",
            "prompt": "Send keywords — <b>one per line</b>. Messages containing one of them are NOT forwarded. "
                      "Prefix with <code>re:</code> for a regex."},
}


def batch_text(bid: int, b: dict) -> str:
    def names(items):
        return ", ".join(esc(i["name"]) for i in items) or "<i>none</i>"

    def kws(items):
        return ", ".join(f"<code>{esc(k)}</code>" for k in items) or "<i>none</i>"

    lines = [f"<b>Batch #{bid}</b> — {'▶️ active' if b['enabled'] else '⏸ paused'}",
             f"📡 Sources ({len(b['sources'])}): {names(b['sources'])}",
             f"🎯 Targets ({len(b['targets'])}): {names(b['targets'])}",
             f"✅ Include: {kws(b['filter_keywords'])}",
             f"🚫 Exclude: {kws(b['exclude_keywords'])}"]
    if b["filter_keywords"] and b["exclude_keywords"]:
        lines.append(f"⚖️ Matches both → <b>{'SEND' if b['conflict_policy'] == 'send' else 'DON’T SEND'}</b>")
    if b["target_members"]:
        lines.append("👤 Only senders: " + ", ".join(f"{esc(m['name'])} (<code>{m['id']}</code>)" for m in b["target_members"]))
    return "\n".join(lines)


def batch_view(bid: int):
    b = batches[bid]
    policy = "SEND" if b["conflict_policy"] == "send" else "DON’T SEND"
    rows = [
        [Button.inline(f"📡 Sources ({len(b['sources'])})", f"f:{bid}:src"), Button.inline(f"🎯 Targets ({len(b['targets'])})", f"f:{bid}:tgt")],
        [Button.inline(f"✅ Include ({len(b['filter_keywords'])})", f"f:{bid}:inc"), Button.inline(f"🚫 Exclude ({len(b['exclude_keywords'])})", f"f:{bid}:exc")],
        [Button.inline(f"👤 Members ({len(b['target_members'])})", f"f:{bid}:mem"), Button.inline(f"⚖️ Both match: {policy}", f"cp:{bid}")],
        [Button.inline("▶️ Resume" if not b["enabled"] else "⏸ Pause", f"pz:{bid}"), Button.inline("📥 Bulk forward", f"bk:{bid}")],
        [Button.inline("🗑 Delete", f"dl:{bid}"), Button.inline("⬅️ Back", "m:list")],
    ]
    return batch_text(bid, b), rows


def editor_view(bid: int, fld: str):
    meta, b = FIELDS[fld], batches[bid]
    items = b[meta["key"]]
    if meta["kind"] == "kw":
        labels = [str(i) for i in items]
    else:
        labels = [str(i["name"]) for i in items]
    body = "\n".join(f"{n + 1}. {esc(l)}" for n, l in enumerate(labels)) or "<i>empty</i>"
    rows = [[Button.inline(f"❌ {l[:40]}", f"fr:{bid}:{fld}:{n}")] for n, l in enumerate(labels)]
    rows.append([Button.inline("➕ Add", f"fa:{bid}:{fld}")])
    rows.append([Button.inline("⬅️ Back to batch", f"b:{bid}")])
    return f"<b>Batch #{bid} — {meta['title']}</b>\n{body}\n\nTap ❌ to remove an item.", rows


def batches_view():
    if not batches:
        return "📭 No batches yet. Create one with “📦 New Batch”.", main_menu()
    rows = []
    for bid, b in sorted(batches.items()):
        src = (b["sources"][0]["name"] + (f" +{len(b['sources']) - 1}" if len(b["sources"]) > 1 else "")) if b["sources"] else "—"
        rows.append([Button.inline(f"{'▶️' if b['enabled'] else '⏸'} #{bid} · {src[:22]} → {len(b['targets'])}", f"b:{bid}")])
    rows.append([Button.inline("⬅️ Back", "m:home")])
    return "📋 <b>Your batches</b> — tap one to edit it.", rows


def source_mode(sid: int) -> str:
    ub = S.authorized and S.enabled
    if bot_access.get(sid, True):
        return "🤖 bot" + (" + 👤 userbot (bot-authored msgs)" if ub else "")
    return "👤 userbot only" if ub else "⚠️ NOT captured (bot can't see it, userbot off)"


def status_text() -> str:
    act = sum(1 for b in batches.values() if b["enabled"])
    srcs = all_sources()
    lines = [f"📊 <b>Status</b>\nBatches: {len(batches)} (active {act}) · Sources: {len(srcs)}",
             f"Since start — forwarded: {STATS['forwarded']} · filtered: {STATS['filtered']} · "
             f"deleted: {STATS['deleted']} · errors: {STATS['errors']}"]
    if not S.authorized:
        lines.append("Userbot: ❌ not logged in")
    else:
        lines.append("Userbot: " + ("🟢 ON" if S.enabled else "⚪ logged in, switched OFF"))
    if srcs:
        lines.append("\n<b>Sources</b>")
        lines += [f"• {esc(n)} — {source_mode(sid)}" for sid, n in srcs.items()]
    return "\n".join(lines)


HELP = (
    "<b>🤖 Auto-Forwarder v8</b>\n\n"
    "<b>Batch</b> = sources → targets + rules. Add several sources for “many → one”, several targets for "
    "“one → many”.\n\n"
    "<b>Keyword rules</b> (case-insensitive; <code>re:</code> prefix = regex; searched in text, caption, "
    "file name and button labels)\n"
    "• Include: forward only messages containing one of them\n"
    "• Exclude: never forward messages containing one of them\n"
    "• Both set and a message matches both → follows your “Both match: SEND / DON’T SEND” switch\n\n"
    "<b>Member filter</b>: only forward messages written by chosen members.\n\n"
    "<b>Userbot</b>: log in once; it captures bot-authored messages and sources the bot can’t see. It must be a "
    "member/admin of the targets it sends to. ON/OFF switch is saved.\n\n"
    "<b>Bulk forward</b>: pick a batch, then send the first and last message of a range (forward them or paste "
    "their links). Filters apply; messages already copied are skipped.\n\n"
    "<b>Requirements</b>: bot = admin in channels; in groups admin or privacy OFF (otherwise the userbot takes over). "
    "Albums, edits and deletions are synced. Copies made by this bot are never forwarded again (no loops).\n\n"
    "Commands: /start /status /help /cancel /setupuserbot /toggleuserbot /logoutuserbot"
)

# ════════════════════════════ RESOLVING CHATS / MEMBERS ═════════════════
INVITE_RE = re.compile(r"(?:https?://)?t\.me/(?:joinchat/|\+)([\w-]+)", re.I)
USERNAME_RE = re.compile(r"(?:https?://)?t\.me/([A-Za-z]\w{3,31})(?:/\d+)?/?$", re.I)
CLINK_RE = re.compile(r"(?:https?://)?t\.me/c/(\d+)(?:/\d+)?", re.I)
MSG_LINK_RE = re.compile(r"(?:https?://)?t\.me/(?:c/(\d+)|([A-Za-z]\w{3,31}))/(\d+)", re.I)


async def get_entity_any(ref):
    last: Optional[Exception] = None
    for c in (bot_client, S.user_client if S.authorized else None):
        if c is None:
            continue
        try:
            return await c.get_entity(ref)
        except Exception as e:
            last = e
    raise ValueError(f"Could not resolve it ({last}). Make sure the bot (or the logged-in userbot) is in that chat.")


def _ent_name(ent) -> str:
    return (getattr(ent, "title", None) or getattr(ent, "first_name", None)
            or getattr(ent, "username", None) or str(ent.id))


async def _chat_from_entity(ent) -> Tuple[int, str]:
    if isinstance(ent, User):
        raise ValueError("That is a user, not a channel/group.")
    return utils.get_peer_id(ent), _ent_name(ent)


async def resolve_channel_input(msg) -> Tuple[int, str]:
    fwd = getattr(msg, "fwd_from", None)
    ch = getattr(getattr(fwd, "from_id", None), "channel_id", None) if fwd else None
    if ch:
        cid = canonical_id(ch)
        try:
            return cid, _ent_name(await get_entity_any(cid))
        except ValueError:
            return cid, str(cid)
    text = (msg.text or "").strip()
    if not text:
        raise ValueError("Forward a message from the chat, or send its @username / invite link / t.me/c link / numeric ID.")
    if (m := CLINK_RE.search(text)):
        return await _chat_from_entity(await get_entity_any(canonical_id(int(m.group(1)))))
    if (m := INVITE_RE.search(text)):
        return await _resolve_invite(m.group(1))
    if text.startswith("@") and len(text) > 1:
        return await _chat_from_entity(await _by_username(text[1:]))
    if (m := USERNAME_RE.search(text)):
        return await _chat_from_entity(await _by_username(m.group(1)))
    if re.fullmatch(r"-?\d+", text):
        return await _chat_from_entity(await get_entity_any(canonical_id(int(text))))
    raise ValueError("Couldn't recognise that. Send a forwarded message, @username, invite link, "
                     "t.me/c/… link or numeric ID (groups: forwarding only reveals the sender, so use a link or ID).")


async def _by_username(uname: str):
    try:
        return await get_entity_any(uname)
    except ValueError as e:
        raise ValueError(f"@{uname}: {e}")


async def _resolve_invite(h: str) -> Tuple[int, str]:
    c = S.user_client if S.authorized else bot_client      # bots can't use invite links
    try:
        res = await c(CheckChatInviteRequest(h))
    except (InviteHashExpiredError, InviteHashInvalidError):
        raise ValueError("That invite link is invalid or expired.")
    except Exception as e:
        raise ValueError(f"Could not check the invite link ({e}). Log in the userbot, or use the numeric ID.")
    chat = res.chat if isinstance(res, (ChatInviteAlready, ChatInvitePeek)) else None
    if chat is None:
        if c is bot_client:
            raise ValueError("Bots can't join via invite links. Log in the userbot (it can join) or use the numeric ID.")
        try:
            updates = await c(ImportChatInviteRequest(h))
            chat = updates.chats[0]
        except UserAlreadyParticipantError:
            raise ValueError("Already a member, but Telegram didn't return the chat — send its numeric ID instead.")
        except Exception as e:
            raise ValueError(f"Could not join via invite link ({e}).")
    return utils.get_peer_id(chat), _ent_name(chat)


async def resolve_member_input(msg) -> Tuple[int, str]:
    fwd = getattr(msg, "fwd_from", None)
    if fwd:
        if isinstance(getattr(fwd, "from_id", None), PeerUser):
            uid = fwd.from_id.user_id
            try:
                return uid, _ent_name(await get_entity_any(uid))
            except ValueError:
                return uid, str(uid)
        if getattr(fwd, "from_name", None):
            raise ValueError("That user hides forward attribution — send their numeric ID or @username.")
    text = (msg.text or "").strip()
    if text.startswith("@") and len(text) > 1:
        try:
            ent = await get_entity_any(text[1:])
        except ValueError as e:
            raise ValueError(f"{text}: {e}")
        return ent.id, _ent_name(ent)
    if re.fullmatch(r"\d+", text):
        uid = int(text)
        try:
            return uid, _ent_name(await get_entity_any(uid))
        except ValueError:
            return uid, str(uid)
    raise ValueError("Send the member's numeric ID, @username, or forward a message from them.")


async def parse_msg_ref(msg) -> Tuple[int, int]:
    """(chat_id, message_id) from a forwarded channel post or a t.me message link."""
    fwd = getattr(msg, "fwd_from", None)
    ch = getattr(getattr(fwd, "from_id", None), "channel_id", None) if fwd else None
    if ch and getattr(fwd, "channel_post", None):
        return canonical_id(ch), fwd.channel_post
    if (m := MSG_LINK_RE.search(msg.text or "")):
        if m.group(1):
            return canonical_id(int(m.group(1))), int(m.group(3))
        ent = await get_entity_any(m.group(2))
        return utils.get_peer_id(ent), int(m.group(3))
    raise ValueError("Forward a message from the source channel, or paste its link (t.me/c/…/123 or t.me/name/123).")


# ════════════════════════════ BULK FORWARD ══════════════════════════════
async def do_bulk(report_chat: int, bid: int, sid: int, first: int, last: int):
    batch = batches.get(bid)
    if not batch:
        return
    if bot_access.get(sid, True):
        client = bot_client
    elif S.authorized and S.enabled:
        client = S.user_client
    else:
        await bot_client.send_message(report_chat, "❌ The bot account can't read that source and the userbot is "
                                                   "off — turn the userbot ON (it must be in the source).")
        return
    sent = failed = scanned = 0
    for start in range(first, last + 1, 100):
        ids = list(range(start, min(start + 100, last + 1)))
        try:
            msgs = await client.get_messages(sid, ids=ids)
        except FloodWaitError as e:
            await asyncio.sleep(e.seconds + 1)
            msgs = await client.get_messages(sid, ids=ids)
        except Exception as e:
            await bot_client.send_message(report_chat, f"❌ <b>Bulk forward failed</b>: {esc(e)}", buttons=main_menu())
            return
        msgs = [m for m in msgs if m and not isinstance(m, MessageService)]
        for group in group_albums(msgs):
            scanned += 1
            try:
                s, f = await run_serial(sid, lambda g=group: deliver(g, sid, client, only_batch=batch))
                sent += s
                failed += f
            except Exception as e:
                failed += 1
                log.error(f"bulk {group[0].id}: {e}")
    await bot_client.send_message(
        report_chat, f"✅ <b>Bulk forward done</b> — batch #{bid}\nRange {first} → {last}\n"
                     f"Messages scanned: {scanned} · copies sent: {sent} · failures: {failed}\n"
                     f"<i>(filtered-out messages and ones already copied are skipped)</i>", buttons=main_menu())


# ════════════════════════════ USERBOT LOGIN ═════════════════════════════
async def login_start(event):
    if S.authorized:
        me = await S.user_client.get_me()
        await say(event, f"🟢 Already logged in as {esc(me.first_name)}.", main_menu())
        return
    login_sessions[event.sender_id] = {"state": "phone"}
    await say(event, "📱 <b>Step 1</b> — send your phone number with country code, e.g. <code>+919876543210</code>.",
              [[Button.inline("❌ Cancel", "lc")]])


async def login_step(event):
    uid = event.sender_id
    sess = login_sessions[uid]
    text = (event.message.text or "").strip()
    cancel = [[Button.inline("❌ Cancel", "lc")]]
    if text.lower() == "/cancel":
        login_sessions.pop(uid, None)
        await event.respond("❌ Login cancelled.", buttons=main_menu())
        return
    uc = S.user_client
    if sess["state"] == "phone":
        if not text.startswith("+"):
            await event.respond("❌ Start with +countrycode, e.g. +919876543210.")
            return
        try:
            if not uc.is_connected():
                await uc.connect()
            await uc.send_code_request(text)
        except PhoneNumberInvalidError:
            login_sessions.pop(uid, None)
            await event.respond("❌ Invalid phone number.")
            return
        except Exception as e:
            login_sessions.pop(uid, None)
            await event.respond(f"❌ {esc(e)}")
            return
        sess.update(phone=text, state="code")
        await event.respond(
            "📩 <b>Step 2</b> — send the code <b>with dashes between the digits</b>, e.g. <code>1-2-3-4-5</code>.\n"
            "<i>Telegram instantly expires codes that are typed in plain digits inside Telegram.</i>", buttons=cancel)
    elif sess["state"] == "code":
        code = re.sub(r"\D", "", text)
        try:
            await uc.sign_in(sess["phone"], code)
        except SessionPasswordNeededError:
            sess["state"] = "password"
            await event.respond("🔐 <b>2FA</b> — send your password.", buttons=cancel)
            return
        except PhoneCodeInvalidError:
            await event.respond("❌ Wrong code, try again (use dashes: 1-2-3-4-5).")
            return
        except PhoneCodeExpiredError:
            try:
                await uc.send_code_request(sess["phone"])
                await event.respond("⌛ Code expired — I sent a <b>new</b> one. Send it with dashes (1-2-3-4-5).", buttons=cancel)
            except Exception as e:
                login_sessions.pop(uid, None)
                await event.respond(f"❌ Expired and resend failed: {esc(e)}\nWait 10–15 min, then /setupuserbot.")
            return
        except Exception as e:
            login_sessions.pop(uid, None)
            await event.respond(f"❌ Login failed: {esc(e)}")
            return
        await _finalize_login(uid, event)
    elif sess["state"] == "password":
        try:
            await uc.sign_in(password=text)
        except PasswordHashInvalidError:
            await event.respond("❌ Wrong password, try again.")
            return
        except Exception as e:
            login_sessions.pop(uid, None)
            await event.respond(f"❌ Login failed: {esc(e)}")
            return
        await _finalize_login(uid, event)


async def _finalize_login(uid, event):
    login_sessions.pop(uid, None)
    S.authorized, S.enabled = True, True
    await db_save_userbot_enabled(True)
    me = await S.user_client.get_me()
    log.info(f"👤 userbot logged in as {me.first_name}")
    await activate_userbot()
    _spawn(refresh_access())
    await event.respond(f"✅ <b>Userbot logged in and ON</b> — {esc(me.first_name)}", buttons=main_menu())


async def userbot_toggle(event):
    if not S.authorized:
        await say(event, "❌ Not logged in yet.", main_menu())
        return
    S.enabled = not S.enabled
    await db_save_userbot_enabled(S.enabled)
    if S.enabled:
        _spawn(warm_userbot())
    await say(event, "🟢 Userbot <b>ON</b>." if S.enabled else "⚪ Userbot <b>OFF</b> (still logged in).", main_menu())


async def userbot_logout(event):
    if not S.authorized:
        await say(event, "ℹ️ Userbot isn't logged in.", main_menu())
        return
    old = S.user_client
    try:
        await old.log_out()
    except Exception as e:
        log.error(f"logout: {e}")
    try:
        await old.disconnect()
    except Exception:
        pass
    for f in ("forwarder_user_session.session", "forwarder_user_session.session-journal"):
        try:
            os.remove(f)
        except OSError:
            pass
    S.user_client = new_user_client()        # old object can't be reused after log_out()
    S.handlers_ready = False                 # handlers were bound to the old object
    S.runner = None
    S.authorized = S.enabled = False
    await db_save_userbot_enabled(False)
    await say(event, "🚪 Userbot logged out.", main_menu())


# ════════════════════════════ COMMANDS ══════════════════════════════════
async def cmd_start(event):
    sessions.pop(event.sender_id, None)
    await event.respond("👋 <b>Channel Auto-Forwarder v8</b>\nUse the buttons below.", buttons=main_menu())


async def cmd_cancel(event):
    sessions.pop(event.sender_id, None)
    login_sessions.pop(event.sender_id, None)
    await event.respond("Cancelled.", buttons=main_menu())


COMMANDS = {
    "start": cmd_start, "menu": cmd_start, "cancel": cmd_cancel,
    "help": lambda e: say(e, HELP, main_menu()),
    "status": lambda e: say(e, status_text(), main_menu()),
    "setupuserbot": login_start, "toggleuserbot": userbot_toggle, "logoutuserbot": userbot_logout,
}


@bot_client.on(events.NewMessage(pattern=r"^/(\w+)(?:@\w+)?\s*$", func=lambda e: e.is_private))
@admin_only
async def on_command(event):
    fn = COMMANDS.get(event.pattern_match.group(1).lower())
    if fn:
        await fn(event)


# ════════════════════════════ BUTTON HANDLER ════════════════════════════
def _batch(bid) -> dict:
    b = batches.get(int(bid))
    if not b:
        raise ValueError("Batch not found (maybe deleted).")
    return b


async def _bulk_prompt(event, uid, bid, idx):
    b = _batch(bid)
    src = b["sources"][idx]
    sessions[uid] = {"type": "bulk", "bid": int(bid), "src": src["id"], "stage": "first", "report_chat": event.chat_id}
    await say(event, f"📥 <b>Bulk forward — batch #{bid}</b>\nSource: {esc(src['name'])}\n\n"
                     "Step 1: send the <b>FIRST</b> message of the range (forward it, or paste its link).",
              [[Button.inline("❌ Cancel", f"b:{bid}")]])


@bot_client.on(events.CallbackQuery())
@admin_only
async def on_callback(event):
    try:
        await event.answer()
    except Exception:
        pass
    uid = event.sender_id
    parts = event.data.decode().split(":")
    act = parts[0]
    sessions.pop(uid, None)                    # pressing any button ends a pending text-input step
    try:
        if act == "m":
            sub = parts[1]
            if sub == "home":
                await say(event, "👋 <b>Channel Auto-Forwarder v8</b>", main_menu())
            elif sub == "new":
                bid = await db_next_id()
                batches[bid] = new_batch()
                await db_save_batch(bid, batches[bid])
                text, rows = batch_view(bid)
                await say(event, text + "\n\n👉 Start with 📡 Sources and 🎯 Targets.", rows)
            elif sub == "list":
                await say(event, *batches_view())
            elif sub == "status":
                await say(event, status_text(), main_menu())
            elif sub == "help":
                await say(event, HELP, main_menu())
            elif sub == "ub_login":
                await login_start(event)
            elif sub == "ub_toggle":
                await userbot_toggle(event)
            elif sub == "ub_logout":
                await userbot_logout(event)
        elif act == "lc":
            login_sessions.pop(uid, None)
            await say(event, "❌ Login cancelled.", main_menu())
        elif act == "b":
            _batch(parts[1])
            await say(event, *batch_view(int(parts[1])))
        elif act == "f":
            _batch(parts[1])
            await say(event, *editor_view(int(parts[1]), parts[2]))
        elif act == "fa":
            bid, fld = int(parts[1]), parts[2]
            _batch(bid)
            sessions[uid] = {"type": "add", "bid": bid, "field": fld}
            await say(event, f"<b>Batch #{bid} — {FIELDS[fld]['title']}</b>\n\n{FIELDS[fld]['prompt']}",
                      [[Button.inline("⬅️ Back", f"f:{bid}:{fld}")]])
        elif act == "fr":
            bid, fld, idx = int(parts[1]), parts[2], int(parts[3])
            b = _batch(bid)
            lst = b[FIELDS[fld]["key"]]
            if 0 <= idx < len(lst):
                lst.pop(idx)
                await db_save_batch(bid, b)
            await say(event, *editor_view(bid, fld))
        elif act == "cp":
            b = _batch(parts[1])
            b["conflict_policy"] = "skip" if b["conflict_policy"] == "send" else "send"
            await db_save_batch(int(parts[1]), b)
            await say(event, *batch_view(int(parts[1])))
        elif act == "pz":
            b = _batch(parts[1])
            b["enabled"] = not b["enabled"]
            await db_save_batch(int(parts[1]), b)
            await say(event, *batch_view(int(parts[1])))
        elif act == "dl":
            _batch(parts[1])
            await say(event, f"🗑 Delete batch #{parts[1]}? Already forwarded copies stay where they are.",
                      [[Button.inline("✅ Yes, delete", f"dy:{parts[1]}"), Button.inline("❌ No", f"b:{parts[1]}")]])
        elif act == "dy":
            bid = int(parts[1])
            batches.pop(bid, None)
            await col_batches.delete_one({"_id": bid})
            await say(event, f"✅ Batch #{bid} deleted.", main_menu())
        elif act == "bk":
            b = _batch(parts[1])
            if not b["sources"] or not b["targets"]:
                await say(event, "❌ The batch needs at least one source and one target.", [[Button.inline("⬅️ Back", f"b:{parts[1]}")]])
            elif len(b["sources"]) == 1:
                await _bulk_prompt(event, uid, parts[1], 0)
            else:
                rows = [[Button.inline(s["name"][:40], f"bks:{parts[1]}:{i}")] for i, s in enumerate(b["sources"])]
                rows.append([Button.inline("⬅️ Back", f"b:{parts[1]}")])
                await say(event, "📥 Bulk forward — which source?", rows)
        elif act == "bks":
            await _bulk_prompt(event, uid, parts[1], int(parts[2]))
    except ValueError as e:
        await say(event, f"❌ {esc(e)}", main_menu())
    except Exception as e:
        log.exception(f"callback {event.data!r}")
        await say(event, f"❌ Error: {esc(e)}", main_menu())


# ════════════════════════════ TEXT INPUT (add items / bulk range) ═══════
async def handle_add(event, sess):
    bid, fld = sess["bid"], sess["field"]
    b = batches.get(bid)
    if not b:
        sessions.pop(event.sender_id, None)
        await event.respond("❌ Batch no longer exists.", buttons=main_menu())
        return
    meta, msg, notes = FIELDS[fld], event.message, []
    try:
        lst = b[meta["key"]]
        if meta["kind"] == "chat":
            cid, name = await resolve_channel_input(msg)
            other = b["targets"] if fld == "src" else b["sources"]
            if any(x["id"] == cid for x in lst):
                raise ValueError("Already in this list.")
            if any(x["id"] == cid for x in other):
                raise ValueError("A chat can't be both source and target of the same batch (it would loop).")
            lst.append({"id": cid, "name": name})
            added = esc(name)
            if fld == "src":
                bot_access[cid] = await check_bot_access(cid)
                if not bot_access[cid]:
                    notes.append("⚠️ The <b>bot account can't see this chat</b> (not admin / privacy mode). "
                                 + ("The userbot will capture it — make sure it is a member of this source and of every target."
                                    if S.authorized else "Log in the userbot, otherwise nothing will be forwarded."))
        elif meta["kind"] == "member":
            uid_, name = await resolve_member_input(msg)
            if any(x["id"] == uid_ for x in lst):
                raise ValueError("Already in this list.")
            lst.append({"id": uid_, "name": name})
            added = f"{esc(name)} (<code>{uid_}</code>)"
        else:
            lines = [l.strip() for l in (msg.text or "").splitlines() if l.strip()]
            if not lines:
                raise ValueError("Send at least one keyword (plain text).")
            for l in lines:
                if l[:3].lower() == "re:":
                    try:
                        re.compile(l[3:])
                    except re.error as e:
                        raise ValueError(f"Invalid regex “{l}”: {e}")
            new = [l for l in dict.fromkeys(lines) if l.casefold() not in {k.casefold() for k in lst}]
            if not new:
                raise ValueError("Those keywords are already in the list.")
            lst.extend(new)
            added = ", ".join(f"<code>{esc(k)}</code>" for k in new)
    except ValueError as e:
        await event.respond(f"❌ {esc(e)}")
        return
    except Exception as e:
        log.exception("handle_add")
        await event.respond(f"❌ Error: {esc(e)}")
        return
    await db_save_batch(bid, b)
    text, rows = editor_view(bid, fld)
    await event.respond("✅ Added: " + added + ("\n" + "\n".join(notes) if notes else "")
                        + "\n\nSend another, or tap Back when done.\n\n" + text, buttons=rows, link_preview=False)


async def handle_bulk_input(event, sess):
    uid = event.sender_id
    try:
        chat_id, msg_id = await parse_msg_ref(event.message)
    except ValueError as e:
        await event.respond(f"❌ {esc(e)}")
        return
    if not same_chat(chat_id, sess["src"]):
        await event.respond("❌ That message is not from the selected source chat.")
        return
    if sess["stage"] == "first":
        sess.update(first=msg_id, stage="last")
        await event.respond(f"✅ First message: <code>{msg_id}</code>.\nStep 2: send the <b>LAST</b> message of the range.")
        return
    first, last = sorted((sess["first"], msg_id))
    sessions.pop(uid, None)
    await event.respond(f"✅ Range <code>{first}</code> → <code>{last}</code>. Bulk forward started…")
    _spawn(do_bulk(sess["report_chat"], sess["bid"], sess["src"], first, last))


@bot_client.on(events.NewMessage(func=lambda e: e.is_private))
@admin_only
async def on_private(event):
    uid = event.sender_id
    if (event.message.text or "").startswith("/"):
        return                                   # commands are handled by on_command
    if uid in login_sessions:
        await login_step(event)
        return
    sess = sessions.get(uid)
    if not sess:
        await event.respond("Use the menu 👇", buttons=main_menu())
        return
    if sess["type"] == "add":
        await handle_add(event, sess)
    elif sess["type"] == "bulk":
        await handle_bulk_input(event, sess)


# ════════════════════════════ MAIN ══════════════════════════════════════
async def main():
    log.info("Starting Auto-Forwarder v8.0 …")
    await db_init()
    async for d in col_batches.find():
        bid = d.pop("_id")
        legacy = "sources" not in d
        batches[bid] = normalize_batch(d)
        if legacy:
            await db_save_batch(bid, batches[bid])       # persist the upgrade from v7.x layout
    log.info(f"Loaded {len(batches)} batches.")

    await bot_client.start(bot_token=BOT_TOKEN)
    S.bot_me = await bot_client.get_me()
    log.info(f"🤖 Bot: @{S.bot_me.username}")

    await S.user_client.connect()
    S.authorized = await S.user_client.is_user_authorized()
    if S.authorized:
        S.enabled = await db_load_userbot_enabled()
        await activate_userbot()
        me = await S.user_client.get_me()
        log.info(f"👤 Userbot: {me.first_name} — {'ON' if S.enabled else 'logged in, OFF'}")
    else:
        S.enabled = False
        log.info("👤 Userbot not logged in (use the menu or /setupuserbot).")

    await refresh_access()
    if CATCH_UP:
        try:
            await bot_client.catch_up()
        except Exception as e:
            log.debug(f"bot catch_up: {e}")
    _spawn(keepalive_loop())
    try:
        await bot_client.send_message(ADMIN_IDS[0], "✅ <b>Forwarder started.</b>\n\n" + status_text(), buttons=main_menu())
    except Exception:
        pass
    log.info("Running…")
    await bot_client.run_until_disconnected()


if __name__ == "__main__":
    asyncio.run(main())
