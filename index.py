"""
Rocky Store Assistant API  (FastAPI on Vercel serverless)
=========================================================

* Public, free, no API keys, no logins, no admin endpoints.
* Multi-merchant: every request carries the shop's permanent domain in the
  X-Rocky-Shop header and the storefront host in X-Rocky-Host.  All stored data
  is namespaced by shop.
* Merchant settings (WhatsApp number, free-shipping threshold, FAQ ...) are saved
  by Shopify in the merchant's theme and sent by the widget with each call.
  This server never stores a merchant setting or a phone number.
* No secrets on the server.  Analytics are forwarded in the browser (GA4/Meta Pixel);
  the server only keeps anonymous per-shop daily counters.
* State lives in Upstash Redis (REST).  Without the env vars it falls back to
  in-memory storage (local development only).
"""
import hashlib
import html
import http.client
import ipaddress
import json
import logging
import os
import re
import secrets
import socket
import ssl
import threading
import time
import urllib.request
import uuid
from datetime import datetime, timezone
from typing import Any, Dict, List, Optional
from urllib.parse import quote, urlparse

from fastapi import APIRouter, Depends, FastAPI, HTTPException, Request
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import HTMLResponse

log = logging.getLogger("rocky")
logging.basicConfig(level=logging.INFO)

# ----------------------------------------------------------------------------
# Limits
# ----------------------------------------------------------------------------
RATE_READ = 60            # requests / minute / IP for GET
RATE_WRITE = 20           # requests / minute / IP for POST, PUT, DELETE
MAX_BODY = 100 * 1024     # 100 KB
MAX_STR = 500
MAX_ARR = 50
MAX_KEYS = 100
MAX_DEPTH = 6
CAT_TTL = 300             # catalogue cache, seconds
FIT_TTL = 90 * 86400      # fit passports
SQUAD_TTL = 7 * 86400     # squads
RECENT_TTL = 30 * 86400   # recently viewed
ANALYTICS_TTL = 400 * 86400
MAX_PAGES = 5             # catalogue pages of 250
MAX_PAGE_BYTES = 6 * 1024 * 1024
FETCH_BUDGET = 7.0        # seconds for the whole catalogue fetch
API_BASE = os.getenv("ROCKY_API_BASE", "https://rocky-vercel.vercel.app/api").rstrip("/")

# ----------------------------------------------------------------------------
# Storage: Upstash Redis REST, in-memory fallback
# ----------------------------------------------------------------------------


class RedisError(Exception):
    pass


class Upstash:
    def __init__(self, url: str, token: str):
        self.url = url.rstrip("/")
        self.token = token

    def _cmd(self, *args):
        payload = json.dumps([a if isinstance(a, (int, float)) else str(a) for a in args]).encode()
        req = urllib.request.Request(
            self.url, data=payload, method="POST",
            headers={"Authorization": f"Bearer {self.token}", "Content-Type": "application/json"})
        try:
            with urllib.request.urlopen(req, timeout=3) as r:
                out = json.loads(r.read().decode())
        except Exception as e:  # network / auth / parse
            raise RedisError(str(e))
        if isinstance(out, dict) and out.get("error"):
            raise RedisError(str(out["error"]))
        return out.get("result") if isinstance(out, dict) else None

    def get(self, k):
        return self._cmd("GET", k)

    def set(self, k, v, ex=None):
        if ex:
            return self._cmd("SET", k, v, "EX", int(ex))
        return self._cmd("SET", k, v)

    def delete(self, k):
        return self._cmd("DEL", k)

    def incr(self, k):
        return int(self._cmd("INCR", k))

    def expire(self, k, s):
        return self._cmd("EXPIRE", k, int(s))

    def hset(self, k, f, v):
        return self._cmd("HSET", k, f, v)

    def hgetall(self, k) -> Dict[str, str]:
        flat = self._cmd("HGETALL", k) or []
        return dict(zip(flat[::2], flat[1::2]))


class Mem:
    """In-memory stand-in with the same interface (local dev only)."""

    def __init__(self):
        self.d: Dict[str, List[Any]] = {}
        self.lock = threading.Lock()

    def _live(self, k):
        it = self.d.get(k)
        if it and it[1] and it[1] < time.time():
            del self.d[k]
            return None
        return it

    def get(self, k):
        with self.lock:
            it = self._live(k)
            return it[0] if it else None

    def set(self, k, v, ex=None):
        with self.lock:
            self.d[k] = [v, time.time() + ex if ex else 0]
            return "OK"

    def delete(self, k):
        with self.lock:
            return 1 if self.d.pop(k, None) else 0

    def incr(self, k):
        with self.lock:
            it = self._live(k)
            n = int(it[0]) + 1 if it else 1
            self.d[k] = [str(n), it[1] if it else 0]
            return n

    def expire(self, k, s):
        with self.lock:
            it = self._live(k)
            if it:
                it[1] = time.time() + s
            return 1 if it else 0

    def hset(self, k, f, v):
        with self.lock:
            it = self._live(k)
            if not it:
                it = [{}, 0]
                self.d[k] = it
            it[0][f] = v
            return 1

    def hgetall(self, k):
        with self.lock:
            it = self._live(k)
            return dict(it[0]) if it else {}


_URL, _TOKEN = os.getenv("UPSTASH_REDIS_REST_URL"), os.getenv("UPSTASH_REDIS_REST_TOKEN")
if _URL and _TOKEN:
    DB: Any = Upstash(_URL, _TOKEN)
else:
    log.warning("UPSTASH_REDIS_REST_URL / _TOKEN missing: using in-memory storage (local dev only)")
    DB = Mem()


def db(fn, *a, **kw):
    """Run a storage call; storage failure becomes a 503."""
    try:
        return fn(*a, **kw)
    except RedisError as e:
        log.error("redis error: %s", e)
        raise HTTPException(503, "Storage temporarily unavailable")


def jget(key):
    raw = db(DB.get, key)
    if not raw:
        return None
    try:
        return json.loads(raw)
    except ValueError:
        return None


def jset(key, obj, ex=None):
    db(DB.set, key, json.dumps(obj, separators=(",", ":"), ensure_ascii=False), ex)


# ----------------------------------------------------------------------------
# Language lexicon  (ONE data structure: English / Roman Urdu / Urdu script)
# ----------------------------------------------------------------------------
LEX: Dict[str, Any] = {
    # foreign word -> English token the widget's parser already understands
    "words": {
        # colours
        "kala": "black", "kaala": "black", "kali": "black", "kaali": "black",
        "کالا": "black", "کالی": "black", "سیاہ": "black",
        "safed": "white", "safaid": "white", "سفید": "white",
        "neela": "blue", "nila": "blue", "neeli": "blue", "nili": "blue", "نیلا": "blue", "نیلی": "blue",
        "lal": "red", "laal": "red", "لال": "red", "سرخ": "red",
        "hara": "green", "hari": "green", "ہرا": "green", "ہری": "green", "سبز": "green",
        "peela": "yellow", "peeli": "yellow", "پیلا": "yellow", "پیلی": "yellow",
        "bhura": "grey", "bhoora": "grey", "بھورا": "grey", "سرمئی": "grey",
        "gulabi": "pink", "گلابی": "pink",
        "narangi": "orange", "jamni": "purple", "jamuni": "purple",
        # clothing
        "qameez": "shirt", "kameez": "shirt", "qamees": "shirt", "قمیض": "shirt", "شرٹ": "shirt",
        "patloon": "trouser", "pataloon": "trouser", "پتلون": "trouser",
        "joota": "shoes", "jootay": "shoes", "jootey": "shoes", "jooti": "shoes", "juti": "shoes",
        "جوتا": "shoes", "جوتے": "shoes", "جوتی": "shoes",
        # price words
        "sasta": "cheap", "sasti": "cheap", "saste": "cheap", "سستا": "cheap", "سستی": "cheap",
        "mehnga": "premium", "mehenga": "premium", "mahenga": "premium", "مہنگا": "premium",
        # occasions / seasons
        "shaadi": "wedding", "shadi": "wedding", "barat": "wedding", "walima": "wedding", "شادی": "wedding",
        "garmi": "summer", "garmiyon": "summer", "گرمی": "summer",
        "sardi": "winter", "sardiyon": "winter", "سردی": "winter",
        "dawat": "party", "دعوت": "party",
        # direction of a price limit (flipped to sit before the number)
        "andar": "under", "tak": "under", "تک": "under", "اندر": "under",
        # size words
        "naap": "size", "سائز": "size",
    },
    "phrases": {
        "ke andar": "under", "k andar": "under", "se kam": "under", "se neeche": "under",
        "کے اندر": "under", "سے کم": "under",
        "se zyada": "above", "se ziada": "above", "se upar": "above", "سے زیادہ": "above", "سے اوپر": "above",
        "pura set": "outfit", "poora set": "outfit", "head to toe": "outfit",
    },
    "filler": ("chahiye chahiyay chahye dikhao dikhaiye dikha dikhana dikhayen mujhe mjhe mereko hai hain kya ka ki "
               "ke ko ek wala wali wale acha achi bhai yaar batao bataiye dein dijiye den karo lao mein par pe koi "
               "kuch aap rang liye mere meri mera apna hamare کا کی کے کو ہے میں چاہیے دکھائیں دکھاؤ مجھے ایک "
               "والا والی رنگ").split(),
    "roman_markers": ("kala kaala kali safed safaid neela nila hara peela sasta sasti shaadi shadi andar chahiye "
                      "chahiyay dikhao dikhaiye mujhe hazar hazaar kya kitna kitne mein wala wali acha bhai yaar "
                      "joota jootay jooti qameez kameez patloon naap konsa batao bataiye").split(),
    "multipliers": {"k": 1000, "hazar": 1000, "hazaar": 1000, "ہزار": 1000,
                    "lakh": 100000, "lac": 100000, "لاکھ": 100000},
    # canonical (English) vocabulary used for detection
    "colors": ("black white blue navy red maroon green olive grey beige brown pink yellow orange purple cream khaki "
               "tan gold silver mustard teal mint burgundy charcoal ivory lavender peach sky").split(),
    "categories": {
        "shirt": ["shirt", "shirts", "tshirt", "t shirt", "tee", "tees", "polo", "kurta", "kurti"],
        "trouser": ["trouser", "trousers", "pant", "pants", "jeans", "jean", "denim", "chino", "chinos",
                    "jogger", "joggers"],
        "shoes": ["shoes", "shoe", "sneaker", "sneakers", "loafer", "loafers", "boots", "boot", "sandal",
                  "sandals", "chappal", "footwear", "trainers"],
        "jacket": ["jacket", "coat", "blazer", "hoodie", "sweater", "sweatshirt", "bomber"],
        "accessory": ["watch", "belt", "wallet", "cap", "socks", "perfume", "bag"],
    },
    "occasions": {
        "wedding": ["wedding", "formal", "festive", "embroidered", "sherwani"],
        "eid": ["eid", "festive", "kurta"],
        "party": ["party", "evening", "formal"],
        "office": ["office", "formal", "work", "interview"],
        "casual": ["casual", "daily", "everyday"],
        "summer": ["summer", "linen", "cotton", "light"],
        "winter": ["winter", "wool", "fleece", "thermal"],
    },
    "cheap": ["cheap", "cheapest", "affordable", "budget friendly", "lowest"],
    "premium": ["premium", "expensive", "luxury", "highest"],
    "outfit": ["outfit", "outfits", "combo", "outfit set", "full set", "complete set"],
    "size": ["size", "sizes"],
}

DIGIT_TABLE = {ord(c): str(i) for i, c in enumerate("۰۱۲۳۴۵۶۷۸۹")}
DIGIT_TABLE.update({ord(c): str(i) for i, c in enumerate("٠١٢٣٤٥٦٧٨٩")})
URDU_RE = re.compile(r"[\u0600-\u06FF]")
_MULT_NAMES = "|".join(re.escape(k) for k in sorted(LEX["multipliers"], key=len, reverse=True))
MULT_RE = re.compile(r"(\d+(?:\.\d+)?)\s*(" + _MULT_NAMES + r")(?![a-z\u0600-\u06FF])")
TOKEN_SPLIT = re.compile(r"[^a-z0-9\u0600-\u06FF]+")


def norm(s: str) -> str:
    s = (s or "").translate(DIGIT_TABLE).lower()
    return " ".join(t for t in TOKEN_SPLIT.split(s) if t)


def pad(s: str) -> str:
    return f" {norm(s)} "


def has_any(padded: str, words) -> bool:
    return any(f" {norm(w)} " in padded for w in words if norm(w))


def normalize(text: str) -> Dict[str, Any]:
    """Translate Roman Urdu / Urdu into the English the widget's parser understands."""
    t = (text or "").translate(DIGIT_TABLE).lower()
    t = re.sub(r"(\d),(\d{3})", r"\1\2", t)
    t = MULT_RE.sub(lambda m: str(int(round(float(m.group(1)) * LEX["multipliers"][m.group(2)]))), t)
    s = " " + " ".join(x for x in TOKEN_SPLIT.split(t) if x) + " "
    for _ in range(2):
        for phrase in sorted(LEX["phrases"], key=len, reverse=True):
            s = s.replace(f" {phrase} ", f" {LEX['phrases'][phrase]} ")
    filler = set(LEX["filler"])
    out: List[str] = []
    for w in s.split():
        if w in LEX["words"]:
            out.append(LEX["words"][w])
        elif w not in filler:
            out.append(w)
    for i in range(1, len(out)):  # "2000 under" -> "under 2000"
        if out[i] in ("under", "above") and out[i - 1].isdigit() and not (i + 1 < len(out) and out[i + 1].isdigit()):
            out[i - 1], out[i] = out[i], out[i - 1]
    return {"text": " ".join(out)}


def detect_lang(raw: str) -> str:
    if URDU_RE.search(raw or ""):
        return "ur"
    toks = set(norm(raw).split())
    if toks & set(LEX["roman_markers"]):
        return "ro"
    if any(p in pad(raw) for p in (" ke andar ", " se zyada ", " se kam ")):
        return "ro"
    return "en"


def parse_query(text: str) -> Dict[str, Any]:
    n = normalize(text)["text"]
    p = f" {n} "
    out: Dict[str, Any] = {
        "normalized_text": n, "lang": detect_lang(text),
        "colors": [c for c in LEX["colors"] if f" {c} " in p],
        "categories": [], "occasions": [], "max_price": None, "min_price": None, "sort": None,
        "wants_outfit": has_any(p, LEX["outfit"]) or " look " in p and bool(re.search(r"\d{3,}", n)),
        "wants_size": has_any(p, LEX["size"]),
    }
    if "gray" in n.split() and "grey" not in out["colors"]:
        out["colors"].append("grey")
    for cat, words in LEX["categories"].items():
        if has_any(p, words):
            out["categories"].append(cat)
    for occ in LEX["occasions"]:
        if f" {occ} " in p:
            out["occasions"].append(occ)
    m = re.search(r"between\s+(\d+)\s+(?:and|to)\s+(\d+)", n)
    if m:
        out["min_price"], out["max_price"] = float(m.group(1)), float(m.group(2))
    else:
        m = re.search(r"(?:under|below|less than|upto|up to|within|max|maximum|budget)\s+(?:rs\s*|pkr\s*)?(\d+)", n)
        if m:
            out["max_price"] = float(m.group(1))
        m2 = re.search(r"(?:above|over|more than|min|minimum|at least|from)\s+(?:rs\s*|pkr\s*)?(\d+)", n)
        if m2:
            out["min_price"] = float(m2.group(1))
        if out["max_price"] is None and out["min_price"] is None:
            for mm in re.finditer(r"(?<![a-z])(\d{3,7})(?!\d)", n):
                before = n[:mm.start()].split()
                if before and before[-1] in ("size", "sz", "waist", "no"):
                    continue
                out["max_price"] = float(mm.group(1))
                break
    if has_any(p, LEX["cheap"]):
        out["sort"] = "price_asc"
    elif has_any(p, LEX["premium"]):
        out["sort"] = "price_desc"
    return out


# ----------------------------------------------------------------------------
# Request plumbing: body, validation, rate limit, CORS, size cap
# ----------------------------------------------------------------------------
SHOP_RE = re.compile(r"^[a-z0-9][a-z0-9\-]{0,60}\.myshopify\.com$")
HOST_RE = re.compile(r"^(?=.{4,253}$)(?:[a-z0-9](?:[a-z0-9\-]{0,61}[a-z0-9])?\.)+[a-z]{2,63}$")
UID_RE = re.compile(r"^[A-Za-z0-9_\-]{8,64}$")
SID_RE = re.compile(r"^[A-Za-z0-9_\-]{6,16}$")


def sanitize(o: Any, depth: int = 0) -> Any:
    """Cap string length, array size, object size and depth."""
    if depth > MAX_DEPTH:
        return None
    if isinstance(o, str):
        return o[:MAX_STR]
    if isinstance(o, list):
        return [sanitize(x, depth + 1) for x in o[:MAX_ARR]]
    if isinstance(o, dict):
        return {str(k)[:60]: sanitize(v, depth + 1) for k, v in list(o.items())[:MAX_KEYS]}
    if isinstance(o, (int, float, bool)) or o is None:
        return o
    return None


async def get_body(request: Request) -> Dict[str, Any]:
    raw = await request.body()
    if len(raw) > MAX_BODY:
        raise HTTPException(413, "Body too large")
    if not raw.strip():
        return {}
    try:
        data = json.loads(raw)
    except ValueError:
        raise HTTPException(400, "Invalid JSON")
    if not isinstance(data, dict):
        raise HTTPException(400, "JSON object expected")
    return sanitize(data)


def client_ip(request: Request) -> str:
    for h in ("x-vercel-forwarded-for", "x-real-ip", "x-forwarded-for"):
        v = request.headers.get(h)
        if v:
            return v.split(",")[0].strip()[:64]
    return request.client.host if request.client else "0.0.0.0"


def rate_limit(ip: str, write: bool) -> None:
    kind, limit = ("w", RATE_WRITE) if write else ("r", RATE_READ)
    minute = int(time.time() // 60)
    key = f"rl:{kind}:{ip}:{minute}"
    try:
        n = DB.incr(key)
        if n == 1:
            DB.expire(key, 70)
    except RedisError as e:  # fail open, never block shoppers because Redis hiccuped
        log.error("rate limit storage error: %s", e)
        return
    if n > limit:
        raise HTTPException(429, "Too many requests, slow down",
                            headers={"Retry-After": str(max(1, 60 - int(time.time() % 60)))})


class Ctx:
    def __init__(self, shop: str, host: Optional[str], ip: str):
        self.shop, self.host, self.ip = shop, host, ip


def ctx(request: Request) -> Ctx:
    """Rate limit + validate shop (+ host).  Shop may also come from ?shop= (links opened from WhatsApp)."""
    ip = client_ip(request)
    rate_limit(ip, request.method in ("POST", "PUT", "DELETE", "PATCH"))
    shop = (request.headers.get("x-rocky-shop") or request.query_params.get("shop") or "").strip().lower()
    if not SHOP_RE.match(shop):
        raise HTTPException(400, "Missing or invalid X-Rocky-Shop (expected your-store.myshopify.com)")
    host = (request.headers.get("x-rocky-host") or "").strip().lower() or None
    if host and not HOST_RE.match(host):  # rejects ports, IP literals, localhost, odd characters
        raise HTTPException(400, "Invalid storefront host")
    origin = request.headers.get("origin")
    if origin and host:
        oh = (urlparse(origin).hostname or "").lower()
        if oh and oh != host and not oh.endswith(".myshopify.com"):
            log.info("origin mismatch shop=%s host=%s origin=%s", shop, host, oh)  # log only, never block
    return Ctx(shop, host, ip)


def need_host(c: Ctx) -> str:
    if not c.host:
        raise HTTPException(400, "X-Rocky-Host is required for this endpoint")
    return c.host


def num(v: Any, lo: float, hi: float, name: str) -> float:
    try:
        f = float(v)
    except (TypeError, ValueError):
        raise HTTPException(400, f"{name} must be a number")
    if not (lo <= f <= hi) or f != f:
        raise HTTPException(400, f"{name} out of range")
    return f


def check_uid(uid: str) -> str:
    if not UID_RE.match(uid or ""):
        raise HTTPException(400, "Invalid uid")
    return uid


# ----------------------------------------------------------------------------
# Catalogue: safe fetch (SSRF-proof) + compact cache
# ----------------------------------------------------------------------------


class CatalogError(Exception):
    pass


class HostRejected(Exception):
    pass


def resolve_public(host: str) -> str:
    """Resolve host and refuse anything that is not a public internet address."""
    if not HOST_RE.match(host) or host.endswith(".local") or host.endswith(".internal"):
        raise HostRejected("host not allowed")
    try:
        infos = socket.getaddrinfo(host, 443, type=socket.SOCK_STREAM)
    except OSError:
        raise CatalogError("host does not resolve")
    ips = []
    for info in infos:
        ip = ipaddress.ip_address(info[4][0])
        if getattr(ip, "ipv4_mapped", None):
            ip = ip.ipv4_mapped
        if not ip.is_global:
            raise HostRejected("host resolves to a non-public address")
        ips.append(str(ip))
    if not ips:
        raise CatalogError("host does not resolve")
    return ips[0]


class PinnedHTTPS(http.client.HTTPSConnection):
    """HTTPS to a pre-validated IP (blocks DNS rebinding), port 443 only, TLS verified for the host name."""

    def __init__(self, host: str, ip: str, timeout: float):
        super().__init__(host, 443, timeout=timeout, context=ssl.create_default_context())
        self._pin = ip

    def connect(self):
        sock = socket.create_connection((self._pin, 443), self.timeout)
        self.sock = self._context.wrap_socket(sock, server_hostname=self.host)


def fetch_json(host: str, ip: str, path: str, timeout: float) -> Any:
    conn = PinnedHTTPS(host, ip, timeout)
    try:
        conn.request("GET", path, headers={"User-Agent": "rocky-api/1.0", "Accept": "application/json"})
        r = conn.getresponse()
        if r.status != 200:  # redirects are NOT followed
            raise CatalogError(f"status {r.status}")
        raw = r.read(MAX_PAGE_BYTES + 1)
        if len(raw) > MAX_PAGE_BYTES:
            raise CatalogError("page too large")
        return json.loads(raw)
    except (OSError, http.client.HTTPException, ValueError) as e:
        raise CatalogError(str(e))
    finally:
        conn.close()


def infer_category(*texts: str) -> str:
    for t in texts:
        p = pad(t or "")
        for cat, words in LEX["categories"].items():
            if has_any(p, words):
                return cat
    return "other"


def compact(p: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    """Reduce a /products.json product to the few fields we need."""
    if not isinstance(p, dict) or not isinstance(p.get("id"), int):
        return None
    names = [str((o or {}).get("name") or "").lower() for o in (p.get("options") or []) if isinstance(o, dict)]
    ci = next((i for i, n in enumerate(names) if "colo" in n), None)
    si = next((i for i, n in enumerate(names) if "size" in n), None)
    variants = []
    for v in (p.get("variants") or [])[:40]:
        if not isinstance(v, dict) or not isinstance(v.get("id"), int):
            continue
        opts = [v.get("option1"), v.get("option2"), v.get("option3")]
        try:
            price = float(v.get("price") or 0)
        except (TypeError, ValueError):
            price = 0.0
        variants.append([v["id"], price, 1 if v.get("available") else 0,
                         str((opts[ci] if ci is not None else "") or "")[:40],
                         str((opts[si] if si is not None else "") or "")[:20]])
    if not variants:
        return None
    tags = p.get("tags") or []
    if isinstance(tags, str):
        tags = [t.strip() for t in tags.split(",") if t.strip()]
    tags = [str(t)[:30] for t in tags[:10]]
    imgs = p.get("images") or []
    image = imgs[0].get("src", "") if imgs and isinstance(imgs[0], dict) else ""
    title = str(p.get("title") or "Item")[:120]
    return {"id": p["id"], "h": str(p.get("handle") or "")[:120], "t": title,
            "c": infer_category(str(p.get("product_type") or ""), title, " ".join(tags)),
            "tg": tags, "im": image if str(image).startswith("https://") else "", "v": variants}


def load_catalogue(shop: str, host: str) -> List[Dict[str, Any]]:
    """Cached 5 min in Redis, keyed by shop AND host so nobody can poison another store's cache."""
    base = f"cat:{shop}:{host}"
    meta = jget(base)
    if meta and meta.get("n") is not None:
        items: List[Dict[str, Any]] = []
        ok = True
        for i in range(meta["n"]):
            chunk = jget(f"{base}:{i}")
            if chunk is None:
                ok = False
                break
            items.extend(chunk)
        if ok:
            return items
    ip = resolve_public(host)  # raises HostRejected / CatalogError
    started = time.time()
    items = []
    for page in range(1, MAX_PAGES + 1):
        left = FETCH_BUDGET - (time.time() - started)
        if left < 1:
            break
        data = fetch_json(host, ip, f"/products.json?limit=250&page={page}", min(4.0, left))
        if not isinstance(data, dict) or not isinstance(data.get("products"), list):
            raise CatalogError("unexpected catalogue format")
        batch = data["products"]
        items.extend(c for c in (compact(p) for p in batch) if c)
        if len(batch) < 250:
            break
    chunks = [items[i:i + 120] for i in range(0, len(items), 120)]
    for i, ch in enumerate(chunks):
        jset(f"{base}:{i}", ch, CAT_TTL + 30)
    jset(base, {"n": len(chunks), "ts": int(time.time())}, CAT_TTL)
    return items


def catalogue_or_http(c: Ctx) -> List[Dict[str, Any]]:
    host = need_host(c)
    try:
        return load_catalogue(c.shop, host)
    except HostRejected as e:
        raise HTTPException(400, str(e))
    except CatalogError as e:
        log.warning("catalogue unavailable shop=%s host=%s: %s", c.shop, host, e)
        raise HTTPException(503, "Catalogue unavailable")


# ----------------------------------------------------------------------------
# Outfit builder
# ----------------------------------------------------------------------------
SLOTS = [("shirt", 0.35), ("trouser", 0.35), ("shoes", 0.30)]


def pick_variant(item: Dict[str, Any], size: Optional[str], colors: List[str]):
    avail = [v for v in item["v"] if v[2]]
    if not avail:
        return None
    sz = (size or "").lower()

    def ok_size(v):
        return not sz or (v[4] or "").lower() == sz

    def ok_color(v):
        return not colors or any(col in (v[3] or "").lower() for col in colors)

    for pred in (lambda v: ok_size(v) and ok_color(v), ok_size, ok_color):
        m = [v for v in avail if pred(v)]
        if m:
            return min(m, key=lambda v: v[1])
    return min(avail, key=lambda v: v[1])


def build_outfits(items, budget: float, colors: List[str], occasions: List[str], count: int,
                  size: Optional[str], host: str) -> List[Dict[str, Any]]:
    occ_words = [w for o in occasions for w in LEX["occasions"].get(o, [o])]
    by_slot = {slot: [i for i in items if i["c"] == slot and any(v[2] for v in i["v"])] for slot, _ in SLOTS}
    used: Dict[str, set] = {slot: set() for slot, _ in SLOTS}
    outfits: List[Dict[str, Any]] = []
    for _ in range(max(1, min(count, 3))):
        remaining, picks = budget, []
        for idx, (slot, share) in enumerate(SLOTS):
            slot_budget = remaining * share / sum(s for _, s in SLOTS[idx:])  # unspent money rolls forward
            best = None
            for it in by_slot[slot]:
                if it["id"] in used[slot]:
                    continue
                v = pick_variant(it, size, colors)
                if not v or v[1] > slot_budget:
                    continue
                score = (2 if colors and any(c in (v[3] or "").lower() for c in colors) else 0) \
                    + (1 if occ_words and has_any(pad(it["t"] + " " + " ".join(it["tg"])), occ_words) else 0) \
                    + (1 if size and (v[4] or "").lower() == size.lower() else 0)
                key = (score, v[1])
                if best is None or key > best[0]:
                    best = (key, it, v)
            if best is None:
                picks = None
                break
            _, it, v = best
            used[slot].add(it["id"])
            remaining -= v[1]
            picks.append({"slot": slot, "id": v[0], "product_id": it["id"], "title": it["t"], "price": v[1],
                          "color": v[3], "size": v[4], "image": it["im"],
                          "url": f"https://{host}/products/{it['h']}" if it["h"] else ""})
        if not picks:
            break
        total = round(sum(p["price"] for p in picks), 2)
        ids = [{"id": p["id"], "quantity": 1} for p in picks]
        outfits.append({"items": picks, "total": total, "left_over": round(budget - total, 2),
                        "shopify_cart_add": {"items": ids},
                        "cart_permalink": f"https://{host}/cart/" + ",".join(f"{i['id']}:1" for i in ids)})
    return outfits


# ----------------------------------------------------------------------------
# Fit passport
# ----------------------------------------------------------------------------
DEFAULT_CHART = [("S", 60), ("M", 75), ("L", 88), ("XL", 100), ("XXL", 9999)]  # (size, max weight kg)
FIT_SHIFT = {"slim": 0, "regular": 0, "loose": 1, "oversized": 2}


def recommend_size(h_cm: Optional[float], w_kg: Optional[float], fit: str, chart=None) -> Dict[str, Any]:
    chart = chart or DEFAULT_CHART
    if not h_cm and not w_kg:
        raise HTTPException(400, "Send height and/or weight")
    sizes = [s for s, _ in chart]
    if w_kg:
        base = next((i for i, (_, mx) in enumerate(chart) if w_kg <= mx), len(chart) - 1)
    else:
        base = 1 if len(chart) > 1 else 0
    if h_cm:  # height bump
        if h_cm >= 190:
            base += 2
        elif h_cm >= 180:
            base += 1
        elif h_cm <= 160:
            base -= 1
    base = min(max(base, 0), len(chart) - 1)
    idx = min(max(base + FIT_SHIFT.get(fit, 0), 0), len(chart) - 1)
    return {"size": sizes[idx], "base_size": sizes[base], "fit": fit,
            "alternatives": [sizes[i] for i in (idx - 1, idx + 1) if 0 <= i < len(sizes)]}


def read_measurements(b: Dict[str, Any]):
    h = b.get("height_cm")
    if h is None and b.get("height_ft") is not None:
        h = num(b["height_ft"], 3, 8, "height_ft") * 30.48 + num(b.get("height_in") or 0, 0, 11.99, "height_in") * 2.54
    w = b.get("weight_kg")
    if w is None and b.get("weight_lb") is not None:
        w = num(b["weight_lb"], 55, 600, "weight_lb") * 0.45359237
    h = num(h, 100, 230, "height") if h is not None else None
    w = num(w, 25, 250, "weight") if w is not None else None
    fit = str(b.get("fit") or "regular").lower()
    if fit not in FIT_SHIFT:
        raise HTTPException(400, "fit must be slim, regular, loose or oversized")
    return h, w, fit


def read_chart(b: Dict[str, Any]):
    ch = b.get("size_chart")
    if not ch:
        return None
    if not isinstance(ch, list) or len(ch) > 12:
        raise HTTPException(400, "size_chart must be a list of up to 12 rows")
    rows = []
    for r in ch:
        if not isinstance(r, dict) or not r.get("size"):
            raise HTTPException(400, "size_chart rows need size and max_weight_kg")
        rows.append((str(r["size"])[:8], num(r.get("max_weight_kg", 9999), 1, 9999, "max_weight_kg")))
    return sorted(rows, key=lambda x: x[1])


# ----------------------------------------------------------------------------
# FAQ
# ----------------------------------------------------------------------------
BUILTIN_FAQ = [
    {"id": "shipping",
     "keywords": ["shipping", "delivery", "deliver", "dispatch", "courier", "charges", "kitne din", "kab aayega",
                  "shipping charges", "delivery charges", "delivery time"],
     "en": "Delivery time and charges depend on your location. You will see the exact shipping cost at checkout, "
           "and our team can give you an estimate on WhatsApp.",
     "ro": "Delivery ka time aur charges aapki location par depend karte hain. Exact shipping cost checkout par "
           "nazar aa jati hai, aur hamari team WhatsApp par andaza bata sakti hai."},
    {"id": "returns",
     "keywords": ["return", "returns", "exchange", "refund", "wapas", "wapsi", "size issue", "badalna",
                  "return policy"],
     "en": "For returns and exchanges please check our policy page, or message our team and we will help you "
           "with a size exchange.",
     "ro": "Return aur exchange ke liye policy page dekh lein, ya hamari team ko message karein, hum size "
           "exchange mein madad karenge."},
    {"id": "payment",
     "keywords": ["payment", "pay", "cod", "cash on delivery", "jazzcash", "easypaisa", "card", "bank transfer",
                  "paisay", "payment methods"],
     "en": "The payment methods this store accepts (for example Cash on Delivery, JazzCash, Easypaisa or cards) "
           "are shown at checkout.",
     "ro": "Jo payment methods store accept karta hai (jaise Cash on Delivery, JazzCash, Easypaisa ya card) "
           "wo checkout par dikhte hain."},
    {"id": "tracking",
     "keywords": ["track", "tracking", "order status", "where is my order", "mera order", "order kahan"],
     "en": "You will receive a tracking link by email or SMS once your order is dispatched. You can also use the "
           "order status link in your confirmation email.",
     "ro": "Order dispatch hote hi tracking link email ya SMS par mil jata hai. Confirmation email mein order "
           "status link bhi hota hai."},
    {"id": "contact",
     "keywords": ["contact", "support", "help", "human", "agent", "baat karni", "whatsapp", "customer care"],
     "en": "Tap the WhatsApp button to chat with our team.",
     "ro": "Hamari team se baat karne ke liye WhatsApp button dabayein."},
]
FAQ_MSG = {
    "en": "I am not sure about that one. Want to ask our team on WhatsApp?",
    "ro": "Is baare mein pakka nahi pata. WhatsApp par team se pooch lein?",
    "ur": "اس بارے میں یقین نہیں۔ واٹس ایپ پر ٹیم سے پوچھیں؟",
}


def faq_best(text: str, entries: List[Dict[str, Any]]):
    p = pad(normalize(text)["text"]) + pad(text)
    best, score = None, 0
    for e in entries:
        s = 0
        for kw in e["keywords"]:
            k = norm(kw)
            if k and f" {k} " in p:
                s = max(s, len(k))
        if s > score:
            best, score = e, s
    return best, score


# ----------------------------------------------------------------------------
# Cart nudge messages
# ----------------------------------------------------------------------------
NUDGE = {
    "need": {"en": "You are {amount} away from free shipping!", "ro": "Free shipping ke liye bas {amount} aur chahiye!",
             "ur": "مفت شپنگ کے لیے صرف {amount} مزید چاہییں!"},
    "ok": {"en": "You have unlocked free shipping! 🎉", "ro": "Mubarak! Aapki shipping free ho gayi 🎉",
           "ur": "مبارک ہو! آپ کی شپنگ مفت ہو گئی 🎉"},
    "empty": {"en": "Add items to your cart to see your free-shipping progress.",
              "ro": "Free shipping progress dekhne ke liye cart mein items daalein.",
              "ur": "مفت شپنگ دیکھنے کے لیے کارٹ میں آئٹمز ڈالیں۔"},
}


def money(n: float, cur: str) -> str:
    return f"{cur} {n:,.0f}".strip()


# ----------------------------------------------------------------------------
# App
# ----------------------------------------------------------------------------


class BodyLimit:
    """Pure ASGI middleware: reject bodies over 100 KB (Content-Length or streamed)."""

    class TooBig(Exception):
        pass

    def __init__(self, app, limit: int):
        self.app, self.limit = app, limit

    async def _reject(self, send):
        body = b'{"detail":"Body too large"}'
        await send({"type": "http.response.start", "status": 413,
                    "headers": [(b"content-type", b"application/json"), (b"content-length", str(len(body)).encode())]})
        await send({"type": "http.response.body", "body": body})

    async def __call__(self, scope, receive, send):
        if scope["type"] != "http":
            return await self.app(scope, receive, send)
        cl = dict(scope["headers"]).get(b"content-length")
        if cl and cl.isdigit() and int(cl) > self.limit:
            return await self._reject(send)
        seen = 0

        async def limited():
            nonlocal seen
            msg = await receive()
            if msg["type"] == "http.request":
                seen += len(msg.get("body", b""))
                if seen > self.limit:
                    raise BodyLimit.TooBig()
            return msg

        try:
            await self.app(scope, limited, send)
        except BodyLimit.TooBig:
            await self._reject(send)


app = FastAPI(title="Rocky Store Assistant API", version="2.0.0", docs_url="/api/docs", openapi_url="/api/openapi.json")
app.add_middleware(BodyLimit, limit=MAX_BODY)
app.add_middleware(CORSMiddleware, allow_origins=["*"], allow_methods=["*"], allow_headers=["*"],
                   allow_credentials=False, expose_headers=["Retry-After"], max_age=86400)

router = APIRouter(prefix="/api")


@router.get("/health")
def health():
    return {"ok": True, "time": int(time.time()), "storage": "upstash" if isinstance(DB, Upstash) else "memory"}


# ---- parse -----------------------------------------------------------------
@router.post("/parse")
def parse_ep(body: dict = Depends(get_body), c: Ctx = Depends(ctx)):
    text = body.get("text")
    if not isinstance(text, str) or not text.strip():
        raise HTTPException(400, "text is required")
    return parse_query(text)


# ---- outfit ----------------------------------------------------------------
@router.post("/outfit/build")
def outfit_ep(body: dict = Depends(get_body), c: Ctx = Depends(ctx)):
    host = need_host(c)
    budget = num(body.get("budget"), 1, 10_000_000, "budget")
    colors = [str(x).lower() for x in (body.get("colors") or []) if isinstance(x, str)][:10]
    occasions = [str(x).lower() for x in (body.get("occasions") or []) if isinstance(x, str)][:10]
    count = int(num(body.get("count", 3), 1, 3, "count"))
    size = body.get("size") if isinstance(body.get("size"), str) else None
    items = catalogue_or_http(c)
    return {"budget": budget, "outfits": build_outfits(items, budget, colors, occasions, count, size, host)}


# ---- fit passport ----------------------------------------------------------
@router.post("/fit/recommend")
def fit_recommend(body: dict = Depends(get_body), c: Ctx = Depends(ctx)):
    h, w, fit = read_measurements(body)
    return recommend_size(h, w, fit, read_chart(body))


@router.put("/fit/{uid}")
def fit_put(uid: str, body: dict = Depends(get_body), c: Ctx = Depends(ctx)):
    check_uid(uid)
    h, w, fit = read_measurements(body)
    rec = recommend_size(h, w, fit)
    doc = {"height_cm": round(h, 1) if h else None, "weight_kg": round(w, 1) if w else None, **rec}
    jset(f"fit:{c.shop}:{uid}", doc, FIT_TTL)
    return doc


@router.get("/fit/{uid}")
def fit_get(uid: str, c: Ctx = Depends(ctx)):
    check_uid(uid)
    doc = jget(f"fit:{c.shop}:{uid}")
    if not doc:
        raise HTTPException(404, "No fit passport")
    return doc


@router.delete("/fit/{uid}")
def fit_del(uid: str, c: Ctx = Depends(ctx)):
    check_uid(uid)
    db(DB.delete, f"fit:{c.shop}:{uid}")
    return {"ok": True}


# ---- whatsapp --------------------------------------------------------------
@router.post("/whatsapp/link")
def wa_link(body: dict = Depends(get_body), c: Ctx = Depends(ctx)):
    digits = re.sub(r"\D", "", str(body.get("number") or ""))
    number = digits if 7 <= len(digits) <= 15 else ""  # invalid number is ignored, never stored
    lines = ["Hi! I need some help."]
    if body.get("note"):
        lines.append(str(body["note"])[:300])
    msgs = body.get("messages") or []
    if isinstance(msgs, list) and msgs:
        lines.append("\n--- My chat ---")
        for m in msgs[-6:]:
            if isinstance(m, dict):
                who = "Me" if m.get("role") == "user" else "Rocky"
                txt = str(m.get("text") or "")[:200]
            else:
                who, txt = "Me", str(m)[:200]
            if txt.strip():
                lines.append(f"{who}: {txt}")
    cart = body.get("cart")
    if isinstance(cart, dict) and isinstance(cart.get("items"), list) and cart["items"]:
        lines.append("\n--- My cart ---")
        for i in cart["items"][:20]:
            if not isinstance(i, dict):
                continue
            try:
                price = float(i.get("final_line_price", i.get("line_price", 0)) or 0) / 100
            except (TypeError, ValueError):
                price = 0
            name = str(i.get("product_title") or i.get("title") or "Item")[:80]
            var = f" ({i['variant_title']})" if i.get("variant_title") else ""
            lines.append(f"{i.get('quantity', 1)} x {name}{var} - {price:,.0f}")
    text = "\n".join(lines)[:1500]
    return {"url": f"https://wa.me/{number}?text={quote(text)}", "text": text}


# ---- squad vote ------------------------------------------------------------
def squad_doc(c: Ctx, sid: str) -> Dict[str, Any]:
    if not SID_RE.match(sid):
        raise HTTPException(404, "Unknown squad")
    doc = jget(f"squad:{c.shop}:{sid}")
    if not doc:
        raise HTTPException(404, "Unknown squad")
    return doc


def squad_tally(c: Ctx, sid: str, doc: Dict[str, Any]) -> Dict[str, Any]:
    votes = db(DB.hgetall, f"squadv:{c.shop}:{sid}")
    counts: Dict[int, int] = {}
    for v in votes.values():
        try:
            counts[int(v)] = counts.get(int(v), 0) + 1
        except ValueError:
            pass
    return {"title": doc["title"], "total_votes": sum(counts.values()),
            "options": [{"option": i, "name": o.get("name"), "items": o["items"], "votes": counts.get(i, 0)}
                        for i, o in enumerate(doc["outfits"], 1)]}


def squad_cast(c: Ctx, sid: str, option: int, uid: str) -> Dict[str, Any]:
    doc = squad_doc(c, sid)
    if not 1 <= option <= len(doc["outfits"]):
        raise HTTPException(400, "Invalid option")
    field = hashlib.sha256(f"{uid}|{c.ip}".encode()).hexdigest()[:20]  # one voter = uid + IP
    key = f"squadv:{c.shop}:{sid}"
    db(DB.hset, key, field, str(option))
    db(DB.expire, key, SQUAD_TTL)
    return squad_tally(c, sid, doc)


@router.post("/squad")
def squad_create(body: dict = Depends(get_body), c: Ctx = Depends(ctx)):
    outs = body.get("outfits")
    if not isinstance(outs, list) or not 2 <= len(outs) <= 3:
        raise HTTPException(400, "Send 2 or 3 outfits")
    title = str(body.get("title") or "Help me pick!")[:100]
    clean = []
    for o in outs:
        if not isinstance(o, dict) or not isinstance(o.get("items"), list) or not o["items"]:
            raise HTTPException(400, "Each outfit needs items")
        items = []
        for it in o["items"][:10]:
            if isinstance(it, dict):
                try:
                    price = float(it.get("price") or 0)
                except (TypeError, ValueError):
                    price = 0.0
                items.append({"title": str(it.get("title") or "Item")[:120], "price": price})
        if not items:
            raise HTTPException(400, "Each outfit needs items")
        clean.append({"name": str(o.get("name") or "")[:120], "items": items})
    sid = secrets.token_urlsafe(6)
    jset(f"squad:{c.shop}:{sid}", {"title": title, "outfits": clean, "ts": int(time.time())}, SQUAD_TTL)
    urls = [f"{API_BASE}/squad/{sid}/vote/{i}?shop={quote(c.shop)}" for i in range(1, len(clean) + 1)]
    lines = [f"🔥 {title}", "Vote for the best one:"]
    for i, (o, u) in enumerate(zip(clean, urls), 1):
        names = o["name"] or " + ".join(it["title"] for it in o["items"])
        total = sum(it["price"] for it in o["items"])
        lines.append(f"\nOption {i}: {names} ({total:,.0f})\n👉 {u}")
    text = "\n".join(lines)[:1500]
    return {"squad_id": sid, "vote_urls": urls, "text": text, "whatsapp_url": f"https://wa.me/?text={quote(text)}"}


@router.get("/squad/{sid}")
def squad_get(sid: str, c: Ctx = Depends(ctx)):
    return squad_tally(c, sid, squad_doc(c, sid))


@router.post("/squad/{sid}/vote")
def squad_vote(sid: str, body: dict = Depends(get_body), c: Ctx = Depends(ctx)):
    uid = check_uid(str(body.get("uid") or ""))
    try:
        option = int(body.get("option"))
    except (TypeError, ValueError):
        raise HTTPException(400, "option must be an integer")
    return squad_cast(c, sid, option, uid)


PAGE = ("<!doctype html><html><head><meta charset=utf-8>"
        "<meta name=viewport content='width=device-width,initial-scale=1'><title>{title}</title></head>"
        "<body style='font-family:system-ui,sans-serif;max-width:440px;margin:40px auto;padding:0 16px'>{body}</body></html>")


@router.get("/squad/{sid}/vote/{n}", response_class=HTMLResponse)
def squad_vote_page(sid: str, n: int, request: Request, uid: Optional[str] = None, c: Ctx = Depends(ctx)):
    ua = request.headers.get("user-agent", "")
    voter = uid if uid and UID_RE.match(uid) else "wa-" + hashlib.sha256(ua.encode()).hexdigest()[:16]
    try:
        res = squad_cast(c, sid, n, voter)
    except HTTPException as e:
        body = f"<h2>Oops</h2><p>{html.escape(str(e.detail))}</p>"
        return HTMLResponse(PAGE.format(title="Rocky", body=body), status_code=e.status_code,
                            headers={"X-Content-Type-Options": "nosniff"})
    rows = "".join(
        f"<li><b>Option {o['option']}</b>: {html.escape(o['name'] or ' + '.join(i['title'] for i in o['items']))}"
        f" &mdash; {o['votes']} vote(s)</li>" for o in res["options"])
    body = f"<h2>Thanks for voting! ✅</h2><p>{html.escape(res['title'])}</p><ul>{rows}</ul>" \
           f"<p>{res['total_votes']} vote(s) so far.</p>"
    return HTMLResponse(PAGE.format(title="Thanks for voting", body=body),
                        headers={"X-Content-Type-Options": "nosniff", "Cache-Control": "no-store"})


# ---- FAQ -------------------------------------------------------------------
@router.get("/faq")
def faq_list(lang: str = "en", c: Ctx = Depends(ctx)):
    key = "ro" if lang in ("ro", "ur") else "en"
    return {"items": [{"id": f["id"], "keywords": f["keywords"], "answer": f[key]} for f in BUILTIN_FAQ]}


@router.post("/faq/ask")
def faq_ask(body: dict = Depends(get_body), c: Ctx = Depends(ctx)):
    text = body.get("text")
    if not isinstance(text, str) or not text.strip():
        raise HTTPException(400, "text is required")
    lang = body.get("lang") if body.get("lang") in ("en", "ro", "ur") else detect_lang(text)
    merchant = []
    for f in (body.get("faq") or [])[:12]:
        if isinstance(f, dict) and f.get("answer"):
            kws = f.get("keywords") or ""
            kws = kws.split(",") if isinstance(kws, str) else [str(k) for k in kws]
            kws = [k.strip() for k in kws if k and k.strip()]
            if kws:
                merchant.append({"id": "merchant", "keywords": kws, "en": str(f["answer"])[:MAX_STR],
                                 "ro": str(f["answer"])[:MAX_STR]})
    entry, score = faq_best(text, merchant)  # the merchant's answers always win
    source = "merchant"
    if not entry:
        entry, score = faq_best(text, BUILTIN_FAQ)
        source = "builtin"
    if not entry:
        return {"matched": False, "lang": lang, "answer": FAQ_MSG.get(lang, FAQ_MSG["en"]), "suggest_whatsapp": True}
    key = "ro" if (lang in ("ro", "ur") and source == "builtin") else "en"
    return {"matched": True, "id": entry["id"], "source": source, "lang": lang, "answer": entry[key]}


# ---- cart nudge ------------------------------------------------------------
@router.post("/cart/nudge")
def cart_nudge(body: dict = Depends(get_body), c: Ctx = Depends(ctx)):
    cart = body.get("cart")
    if not isinstance(cart, dict):
        raise HTTPException(400, "cart (the /cart.js JSON) is required")
    threshold = num(body.get("threshold"), 0, 100_000_000, "threshold")
    cur = re.sub(r"[^A-Za-z$€£₹.]", "", str(body.get("currency") or ""))[:5]
    lang = body.get("lang") if body.get("lang") in ("en", "ro", "ur") else "en"
    total = num(cart.get("total_price") or 0, 0, 1e12, "total_price") / 100  # minor units
    items = [i for i in (cart.get("items") or []) if isinstance(i, dict)]
    in_cart = {str(i.get("product_id")) for i in items}
    empty = not items
    remaining = max(0.0, threshold - total)
    qualified = (threshold > 0 and remaining <= 0 and not empty)
    msg_key = "empty" if empty else "ok" if qualified else "need"
    message = NUDGE[msg_key][lang].format(amount=money(remaining, cur))
    suggestions: List[Dict[str, Any]] = []
    if not qualified and not empty and remaining > 0 and c.host:
        try:
            pool = [p for p in load_catalogue(c.shop, c.host)
                    if str(p["id"]) not in in_cart and any(v[2] for v in p["v"])]
        except (HostRejected, CatalogError):
            pool = []
        def price(p):
            return min(v[1] for v in p["v"] if v[2])
        fits = sorted([p for p in pool if price(p) >= remaining], key=price)
        near = sorted([p for p in pool if price(p) < remaining], key=lambda p: -price(p))
        for p in (fits + near)[:4]:
            suggestions.append({"id": p["id"], "title": p["t"], "price": price(p), "image": p["im"],
                                "url": f"https://{c.host}/products/{p['h']}" if p["h"] else ""})
    pct = 100 if threshold <= 0 else min(100, int(100 * total / threshold))
    return {"threshold": threshold, "current": total, "remaining": remaining, "qualified": qualified,
            "progress_pct": pct, "message": message, "suggestions": suggestions}


# ---- recently viewed -------------------------------------------------------
@router.post("/recent/{uid}")
def recent_add(uid: str, body: dict = Depends(get_body), c: Ctx = Depends(ctx)):
    check_uid(uid)
    pid = str(body.get("id") or "")[:40]
    if not pid:
        raise HTTPException(400, "id is required")
    image, url = str(body.get("image") or ""), str(body.get("url") or "")
    rec = {"id": pid, "title": str(body.get("title") or "")[:120],
           "url": url if url.startswith("/") or url.startswith("https://") else "",
           "image": image if image.startswith("https://") else "",
           "price": body.get("price") if isinstance(body.get("price"), (int, float)) else None}
    key = f"recent:{c.shop}:{uid}"
    lst = [r for r in (jget(key) or []) if r.get("id") != pid]
    lst.insert(0, rec)
    lst = lst[:20]
    jset(key, lst, RECENT_TTL)
    return {"items": lst}


@router.get("/recent/{uid}")
def recent_get(uid: str, c: Ctx = Depends(ctx)):
    check_uid(uid)
    return {"items": jget(f"recent:{c.shop}:{uid}") or []}


@router.delete("/recent/{uid}")
def recent_del(uid: str, c: Ctx = Depends(ctx)):
    check_uid(uid)
    db(DB.delete, f"recent:{c.shop}:{uid}")
    return {"ok": True}


# ---- analytics (anonymous per-shop daily counters, write-only) -----------------
EVENTS = {"rocky:open", "rocky:minimise", "rocky:end", "rocky:close", "rocky:ask", "rocky:results", "rocky:add"}


async def lenient_json(request: Request) -> Dict[str, Any]:
    """sendBeacon posts text/plain, so parse the raw body whatever the content type is."""
    raw = await request.body()
    if len(raw) > MAX_BODY:
        raise HTTPException(413, "Body too large")
    try:
        data = json.loads(raw or b"{}")
    except ValueError:
        raise HTTPException(400, "Invalid JSON")
    if not isinstance(data, dict):
        raise HTTPException(400, "JSON object expected")
    return sanitize(data)


def count_event(shop: str, name: Any) -> bool:
    if not isinstance(name, str) or name not in EVENTS:  # fixed allow-list: nobody can create arbitrary keys
        return False
    day = datetime.now(timezone.utc).strftime("%Y%m%d")
    key = f"an:{shop}:{day}:{name}"
    try:
        if DB.incr(key) == 1:
            DB.expire(key, ANALYTICS_TTL)
    except RedisError as e:
        log.error("analytics storage error: %s", e)
    return True


def analytics_ctx(request: Request, body: Dict[str, Any]) -> str:
    """Beacons cannot set headers, so for analytics the shop may also be in the body."""
    ip = client_ip(request)
    rate_limit(ip, True)
    shop = (request.headers.get("x-rocky-shop") or body.get("shop") or "").strip().lower()
    if not SHOP_RE.match(shop):
        raise HTTPException(400, "Missing or invalid shop")
    return shop


@router.post("/analytics/event")
async def analytics_event(request: Request):
    body = await lenient_json(request)
    shop = analytics_ctx(request, body)
    return {"ok": count_event(shop, body.get("name"))}


@router.post("/analytics/batch")
async def analytics_batch(request: Request):
    body = await lenient_json(request)
    shop = analytics_ctx(request, body)
    evs = body.get("events") if isinstance(body.get("events"), list) else []
    n = sum(1 for e in evs[:MAX_ARR] if isinstance(e, dict) and count_event(shop, e.get("name")))
    return {"ok": True, "counted": n}


app.include_router(router)
