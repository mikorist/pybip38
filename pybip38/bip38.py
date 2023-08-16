#!/usr/bin/env python
# -*- coding: utf-8 -*-

from __future__ import print_function, division, absolute_import, unicode_literals

import os
import sys
import hashlib
import scrypt
import string
import unicodedata
from binascii import hexlify, unhexlify
from codecs import decode
from Crypto.Cipher import AES
import gmpy2
from gmpy2 import mpz

def simple_aes_encrypt(msg, key):
    assert len(key) == 32
    assert len(msg) == 16
    msg = hexstrlify(msg)  # Stupid hack/workaround for ascii decode errors
    msg = msg + '7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b7b'
    cipher = AES.new(key, AES.MODE_ECB)
    return cipher.encrypt(unhexlify(msg))[:16]

def simple_aes_decrypt(msg, key):
    assert len(msg) == 16
    assert len(key) == 32
    cipher = AES.new(key, AES.MODE_ECB)
    msg = hexstrlify(cipher.decrypt(msg))
    while msg[-2:] == '7b':  # Can't use rstrip for multiple chars
        msg = msg[:-2]
    for i in range((32 - len(msg)) // 2):
        msg = msg + '7b'
    assert len(msg) == 32
    return unhexlify(msg)

COMPRESSION_FLAGBYTES = {'20', '24', '28', '2c', '30', '34', '38', '3c', 'e0', 'e8', 'f0', 'f8'}
LOTSEQUENCE_FLAGBYTES = {'04', '0c', '14', '1c', '24', '2c', '34', '3c'}
NON_MULTIPLIED_FLAGBYTES = {'c0', 'c8', 'd0', 'd8', 'e0', 'e8', 'f0', 'f8'}
EC_MULTIPLIED_FLAGBYTES = {'00', '04', '08', '0c', '10', '14', '18', '1c', '20', '24', '28', '2c', '30', '34', '38', '3c'}
N = gmpy2.mpz("0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141")
P = gmpy2.mpz("0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f")
Gx = gmpy2.mpz("0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")
Gy = gmpy2.mpz("0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8")

# Memoization for ecmultiply
ecmultiply_memo = {}


def ecadd(xp, yp, xq, yq):
    m = ((yq - yp) * modinv(xq - xp, P)) % P
    xr = (m * m - xp - xq) % P
    yr = (m * (xp - xr) - yp) % P
    return xr, yr


def ecsubtract(xp, yp, xq, yq):
    return ecadd(xp, yp, xq, (P - yq) % P)


def ecdouble(xp, yp):
    ln = 3 * xp * xp
    ld = 2 * yp
    lam = (ln * modinv(ld, P)) % P
    xr = (lam**2 - 2 * xp) % P
    yr = (lam * (xp - xr) - yp) % P
    return xr, yr


def ecmultiply(xs, ys, scalar):
    if scalar == 0 or scalar >= N:
        raise Exception("Invalid scalar.")

    if (xs, ys, scalar) in ecmultiply_memo:
        return ecmultiply_memo[(xs, ys, scalar)]

    scalarbin = bin(scalar)[2:]
    Qx, Qy = xs, ys
    for bit in scalarbin[1:]:
        Qx, Qy = ecdouble(Qx, Qy)
        if bit == "1":
            Qx, Qy = ecadd(Qx, Qy, xs, ys)

    ecmultiply_memo[(xs, ys, scalar)] = (Qx, Qy)
    return Qx, Qy


def modinv(a, n=P):
    return gmpy2.invert(a, n)


def pow_mod(x, y, z):
    return gmpy2.powmod(x, y, z)


def strlify(a):
    return a.decode() if isinstance(a, bytes) else str(a)


def hexstrlify(a):
    return hexlify(a).decode()


def hexreverse(a):
    return hexstrlify(unhexlify(a)[::-1])


def isitstring(i):
    if sys.version_info[0] == 2:
        if isinstance(i, str) or isinstance(i, unicode) or isinstance(i, basestring):
            return True
        else:
            return False
    else:
        if isinstance(i, str):
            return True
        else:
            return False


def isitint(i):
    if sys.version_info[0] == 2:
        if isinstance(i, int) or isinstance(i, long):
            return True
        else:
            return False
    else:
        if isinstance(i, int):
            return True
        else:
            return False


def dechex(num, zfill=0):
    if isinstance(num, gmpy2.mpz):
        hex_num = hex(num)[2:]

        if len(hex_num) % 2:
            hex_num = "0" + hex_num

        bytes_o = bytes.fromhex(hex_num)

        if bytes_o == b"\x00":
            bytes_o = b"\x00"

        hex_bytes = bytes_o.hex()
        hex_len = len(hex_bytes)
        zfill_count = 2 * zfill - hex_len

        if zfill_count > 0:
            hex_bytes = "0" * zfill_count + hex_bytes

        return hex_bytes
    else:
        raise TypeError("Input must be mpz.")


def normalize_input(input, preferunicodeoverstring=False, nfconly=False):
    try:
        if nfconly:
            normalized_input = unicodedata.normalize("NFC", input)
        else:
            normalized_input = unicodedata.normalize("NFKD", input)

        if preferunicodeoverstring:
            return normalized_input
        else:
            return str(normalized_input)

    except Exception as e:
        raise Exception("Unable to normalize input:", e)


def privtopub(priv, outcompressed=True):
    x, y = ecmultiply(Gx, Gy, gmpy2.mpz(priv, 16))
    x = format(x, "064x")
    y = format(y, "064x")
    o = "04" + x + y
    if outcompressed:
        return compress(o)
    else:
        return o


def multiplypriv(p1, p2):
    result = (gmpy2.mpz(p1, 16) * gmpy2.mpz(p2, 16)) % N
    return format(result, "064x")


b58_digits = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"


def b58e(b, check=True):
    b = unhexlify(b)
    if check:
        b = b + hashlib.sha256(hashlib.sha256(b).digest()).digest()[:4]
    n = gmpy2.mpz("0x0" + hexlify(b).decode("utf8"), 16)
    res = []
    while n > 0:
        n, r = divmod(n, 58)
        res.append(b58_digits[r])
    res = "".join(res[::-1])

    czero = b"\x00"
    if sys.version_info[0] > 2:
        czero = 0
    pad = 0
    for c in b:
        if c == czero:
            pad += 1
        else:
            break
    o = b58_digits[0] * pad + res
    try:
        o = o.decode("ascii")
    except:
        pass
    return o


def b58d(s, check=True):
    assert s
    n = 0
    for c in s:
        n *= 58
        if c not in b58_digits:
            raise Exception("Character %r is not a valid base58 character" % c)
        digit = b58_digits.index(c)
        n += digit
    h = "%x" % n
    if len(h) % 2:
        h = "0" + h
    res = unhexlify(h.encode("utf8"))
    pad = 0
    for c in s[:-1]:
        if c == b58_digits[0]:
            pad += 1
        else:
            break
    o = b"\x00" * pad + res

    if check:
        assert hashlib.sha256(hashlib.sha256(o[:-4]).digest()).digest()[:4] == o[-4:]
        return hexlify(o[:-4]).decode("utf-8")
    else:
        return hexlify(o).decode("utf-8")


def multiplypub(pub, priv, outcompressed=True):
    if len(pub) == 66:
        pub = uncompress(pub)
    x, y = ecmultiply(
        gmpy2.mpz(pub[2:66], 16), gmpy2.mpz(pub[66:], 16), gmpy2.mpz(priv, 16)
    )
    x = format(x, "064x")
    y = format(y, "064x")
    o = "04" + x + y
    if outcompressed:
        return compress(o)
    else:
        return o


def compress(pub):
    x = pub[2:66]
    y = pub[66:]
    if gmpy2.mpz(y, 16) % 2:
        o = "03" + x
    else:
        o = "02" + x
    return o


def uncompress(pub):
    yp = gmpy2.mpz(pub[:2], 16) - 2
    x = gmpy2.mpz(pub[2:], 16)
    a = (pow_mod(x, 3, P) + 7) % P
    y = pow_mod(a, (P + 1) // 4, P)
    if y % 2 != yp:
        y = -y % P
    x = format(x, "064x")
    y = format(y, "064x")
    return "04" + x + y


def hash160(hexstring):
    h = hashlib.new("ripemd160")
    h.update(hashlib.sha256(unhexlify(hexstring)).digest())
    return hexlify(h.digest()).decode("utf-8")


def hash256(hexstring):
    return hashlib.sha256(hashlib.sha256(unhexlify(hexstring)).digest()).digest().hex()


def pubtoaddress(pub, prefix="00"):
    return b58e(prefix + hash160(pub))


def bip38decrypt(password, encrypted_private_key, outputlotsequence=False):
    password = normalize_input(password, False, True)
    encrypted_private_key = b58d(encrypted_private_key)

    prefix = encrypted_private_key[:4]
    flagbyte = encrypted_private_key[4:6]
    is_compressed = flagbyte in COMPRESSION_FLAGBYTES

    if prefix not in ["0142", "0143"]:
        return (False, False, False) if outputlotsequence else False

    if prefix == "0142":
        salt = unhexlify(encrypted_private_key[6:14])
        msg1, msg2 = unhexlify(encrypted_private_key[14:46]), unhexlify(
            encrypted_private_key[46:]
        )

        scrypthash = hexstrlify(scrypt.hash(password, salt, 16384, 8, 8, 64))
        key = unhexlify(scrypthash[64:])
        msg1, msg2 = hexstrlify(simple_aes_decrypt(msg1, key)), hexstrlify(
            simple_aes_decrypt(msg2, key)
        )

        half1 = gmpy2.mpz(msg1, 16) ^ gmpy2.mpz(scrypthash[:32], 16)
        half2 = gmpy2.mpz(msg2, 16) ^ gmpy2.mpz(scrypthash[32:64], 16)
        priv = dechex(half1, 16) + dechex(half2, 16)

    else:
        owner_entropy = encrypted_private_key[14:30]
        enchalf1half1, enchalf2 = (
            encrypted_private_key[30:46],
            encrypted_private_key[46:],
        )

        lotsequence, owner_salt = (
            (owner_entropy[8:], owner_entropy[:8])
            if flagbyte in LOTSEQUENCE_FLAGBYTES
            else (False, owner_entropy)
        )
        salt = unhexlify(owner_salt)

        prefactor = hexstrlify(scrypt.hash(password, salt, 16384, 8, 8, 32))
        passfactor = hash256(prefactor + owner_entropy) if lotsequence else prefactor

        passpoint = privtopub(passfactor, True)
        password = unhexlify(passpoint)

        salt = unhexlify(encrypted_private_key[6:14] + owner_entropy)
        encseedb = hexstrlify(scrypt.hash(password, salt, 1024, 1, 1, 64))
        key = unhexlify(encseedb[64:])

        tmp = hexstrlify(simple_aes_decrypt(unhexlify(enchalf2), key))
        enchalf1half2_seedblastthird = gmpy2.mpz(tmp, 16) ^ gmpy2.mpz(
            encseedb[32:64], 16
        )
        enchalf1half2_seedblastthird = dechex(enchalf1half2_seedblastthird, 16)
        enchalf1half2 = enchalf1half2_seedblastthird[:16]
        enchalf1 = enchalf1half1 + enchalf1half2

        seedb = hexstrlify(simple_aes_decrypt(unhexlify(enchalf1), key))
        seedb = gmpy2.mpz(seedb, 16) ^ gmpy2.mpz(encseedb[:32], 16)
        seedb = dechex(seedb, 16) + enchalf1half2_seedblastthird[16:]

        factorb = hash256(seedb)
        if not (0 < gmpy2.mpz(factorb, 16) < N):
            return (False, False, False) if outputlotsequence else False

        priv = multiplypriv(passfactor, factorb)

    pub = privtopub(priv, is_compressed)
    privcompress = "01" if is_compressed else ""

    address = pubtoaddress(pub, "00")
    addrhex = (
        hexstrlify(address)
        if isinstance(address, bytes)
        else hexstrlify(bytearray(address, "ascii"))
    )

    addresshash = hash256(addrhex)[:8]

    if addresshash == encrypted_private_key[6:14]:
        priv = b58e("80" + priv + privcompress)

        if outputlotsequence:
            if lotsequence:
                lot = gmpy2.mpz(lotsequence, 16)
                return priv, lot // 4096, lot % 4096
            else:
                return priv, False, False
        else:
            return priv

    return (False, False, False) if outputlotsequence else False


def intermediate_code(
    password, useLotAndSequence=False, lot=100000, sequence=1, owner_salt=os.urandom(8)
):
    # Normalize the input password
    password = normalize_input(password, False, True)

    # Validate the length of owner_salt based on useLotAndSequence flag
    assert len(owner_salt) == 8 or (len(owner_salt) == 4 and useLotAndSequence)

    if useLotAndSequence:
        lot, sequence = gmpy2.mpz(lot), gmpy2.mpz(sequence)

        # Validate lot and sequence values
        assert lot >= 100000 and lot <= 999999
        assert sequence >= 0 and sequence <= 4095

        # Calculate lotsequence and owner_salt
        lotsequence = dechex((lot * 4096 + sequence), 4)
        owner_salt = owner_salt[:4]

        # Calculate prefactor and passfactor
        prefactor = scrypt.hash(password, owner_salt, 16384, 8, 8, 32)
        prefactor = hexstrlify(prefactor)
        owner_entropy = hexstrlify(owner_salt) + lotsequence
        passfactor = hash256(prefactor + owner_entropy)

        # Magic bytes for useLotAndSequence case
        magicbytes = "2CE9B3E1FF39E251"
    else:
        # Calculate passfactor
        passfactor = scrypt.hash(password, owner_salt, 16384, 8, 8, 32)
        passfactor = hexstrlify(passfactor)
        owner_entropy = hexstrlify(owner_salt)

        # Magic bytes for non-useLotAndSequence case
        magicbytes = "2CE9B3E1FF39E253"

    # Calculate passpoint and return the intermediate code
    passpoint = privtopub(passfactor, True)
    return b58e(magicbytes + owner_entropy + passpoint)


def privtohex(key):
    if isitint(key):
        key = dechex(key, 32)
    else:
        try:
            key, z, zz = wiftohex(key)
            assert len(key) == 64
        except:
            try:
                key = unhexlify(key)
            except:
                try:
                    key1 = hexstrlify(key)
                    assert len(key1) == 64 or len(key1) == 66 or len(key1) == 68
                    if len(key1) == 68:
                        assert key1[-2:] == "01"
                    key = key1
                except:
                    raise Exception("Cannot interpret input key.")
            else:
                key = hexstrlify(key)
    if len(key) == 68:
        assert key[-2:] == "01"
        key = key[:-2]
    if len(key) == 66:
        key = key[2:]
    assert len(key) == 64
    return key


def wiftohex(wifkey):
    iscompressed = False
    wifkey = normalize_input(wifkey)
    assert len(wifkey) == 50 or len(wifkey) == 51 or len(wifkey) == 52
    for c in wifkey:
        if c not in b58_digits:
            raise Exception("Not WIF")
    key = b58d(wifkey)
    prefix, key = key[:2], key[2:]
    if len(key) == 66:
        assert key[-2:] == "01"
        key = key[:-2]
        iscompressed = True
    assert len(key) == 64
    return key, prefix, iscompressed


def bip38encrypt(password, priv, iscompressed=False):
    password = normalize_input(password, False, True)
    try:
        priv, prefix, iscompressed = wiftohex(priv)
    except:
        priv = privtohex(priv)
    prefix = "0142"  # Not using EC multiplication
    flagbyte = 224 if iscompressed else 192
    flagbyte_hex = format(flagbyte, "02x")
    pubkey = privtopub(priv, iscompressed)
    address = pubtoaddress(pubkey, "00")
    addrhex = (
        hexstrlify(address)
        if isinstance(address, bytes)
        else hexstrlify(bytearray(address, "ascii"))
    )
    salt = unhexlify(hash256(addrhex)[:8])
    scrypthash = hexstrlify(scrypt.hash(password, salt, 16384, 8, 8, 64))
    msg1 = dechex((gmpy2.mpz(priv[:32], 16) ^ gmpy2.mpz(scrypthash[:32], 16)), 16)
    msg2 = dechex((gmpy2.mpz(priv[32:], 16) ^ gmpy2.mpz(scrypthash[32:64], 16)), 16)
    msg1, msg2 = unhexlify(msg1), unhexlify(msg2)
    key = unhexlify(scrypthash[64:])
    half1 = hexstrlify(simple_aes_encrypt(msg1, key))
    half2 = hexstrlify(simple_aes_encrypt(msg2, key))
    salt = hexstrlify(salt)
    return b58e(prefix + flagbyte_hex + salt + half1 + half2)


def passphrase_to_key(intermediatecode, iscompressed=False, seedb=os.urandom(24)):
    intermediatecode = normalize_input(intermediatecode)
    intermediatecode = b58d(intermediatecode)
    prefix = "0143"
    flagbyte = "20" if iscompressed else "00"

    magicbytes = intermediatecode[:16]
    owner_entropy = intermediatecode[16:32]
    passpoint = intermediatecode[32:]

    if intermediatecode[14:16] == "51":
        flagbyte = "24"

    seedb = hexstrlify(seedb)
    factorb = hash256(seedb)

    newkey = multiplypub(passpoint, factorb, iscompressed)
    address = pubtoaddress(newkey, "00")
    addrhex = hexstrlify(bytearray(address, "ascii"))
    addresshash = hash256(addrhex)[:8]
    salt = unhexlify(addresshash + owner_entropy)

    passpoint = unhexlify(passpoint)
    scrypthash = hexstrlify(scrypt.hash(passpoint, salt, 1024, 1, 1, 64))
    msg1 = dechex(gmpy2.mpz(seedb[:32], 16) ^ gmpy2.mpz(scrypthash[:32], 16), 16)
    key = unhexlify(scrypthash[64:])

    half1 = simple_aes_encrypt(unhexlify(msg1), key)
    msg2 = dechex(
        gmpy2.mpz(hexstrlify(half1)[16:] + seedb[32:], 16)
        ^ gmpy2.mpz(scrypthash[32:64], 16),
        16,
    )
    half2 = simple_aes_encrypt(unhexlify(msg2), key)

    enckey = b58e(
        prefix
        + flagbyte
        + addresshash
        + owner_entropy
        + hexlify(half1).decode()[:16]
        + hexlify(half2).decode()
    )
    pointb = privtopub(factorb, True)
    pointb_prefix = (gmpy2.mpz(scrypthash[126:], 16) & 1) ^ gmpy2.mpz(pointb[:2], 16)
    pointb_prefix = dechex(pointb_prefix)
    msg3 = gmpy2.mpz(pointb[2:34], 16) ^ gmpy2.mpz(scrypthash[:32], 16)
    msg4 = gmpy2.mpz(pointb[34:], 16) ^ gmpy2.mpz(scrypthash[32:64], 16)
    msg3 = unhexlify(dechex(msg3, 16))
    msg4 = unhexlify(dechex(msg4, 16))

    pointb_half1 = simple_aes_encrypt(msg3, key)
    pointb_half2 = simple_aes_encrypt(msg4, key)

    encpointb = (
        pointb_prefix + hexlify(pointb_half1).decode() + hexlify(pointb_half2).decode()
    )
    cfrm38code = b58e("643BF6A89A" + flagbyte + addresshash + owner_entropy + encpointb)

    return enckey, cfrm38code, address


def confirm38code(password, cfrm38code, outputlotsequence=False):
    password = normalize_input(password, False, True)
    cfrm38code = b58d(cfrm38code)
    assert len(cfrm38code) == 102
    assert cfrm38code[:10] == "643BF6A89A"
    flagbyte = cfrm38code[10:12]
    addresshash = cfrm38code[12:20]
    owner_entropy = cfrm38code[20:36]
    encpointb = cfrm38code[36:]

    if flagbyte in LOTSEQUENCE_FLAGBYTES:
        owner_salt = owner_entropy[:8]
        lotsequence = owner_entropy[8:]
    else:
        lotsequence = False
        owner_salt = owner_entropy

    owner_salt = unhexlify(owner_salt)
    prefactor = hexstrlify(scrypt.hash(password, owner_salt, 16384, 8, 8, 32))
    passfactor = (
        hash256(prefactor + owner_entropy)
        if flagbyte in LOTSEQUENCE_FLAGBYTES
        else prefactor
    )

    passfactor_mmpz = gmpy2.mpz(passfactor, 16)
    if passfactor_mmpz == 0 or passfactor_mmpz >= N:
        if outputlotsequence:
            return (False, False, False) if lotsequence else False
        else:
            return False

    passpoint = privtopub(passfactor, True)
    password = unhexlify(passpoint)
    salt = unhexlify(addresshash + owner_entropy)
    scrypthash = hexstrlify(scrypt.hash(password, salt, 1024, 1, 1, 64))
    scrypthash_prefix = scrypthash[:32]
    scrypthash_suffix = scrypthash[32:64]

    msg1 = unhexlify(encpointb[2:34])
    msg2 = unhexlify(encpointb[34:])
    key = unhexlify(scrypthash[64:])
    half1 = simple_aes_decrypt(msg1, key)
    half2 = simple_aes_decrypt(msg2, key)
    half1, half2 = hexstrlify(half1), hexstrlify(half2)

    pointb_half1 = gmpy2.mpz(half1, 16) ^ gmpy2.mpz(scrypthash[:32], 16)
    pointb_half2 = gmpy2.mpz(half2, 16) ^ gmpy2.mpz(scrypthash[32:64], 16)
    pointb_xcoord = dechex(pointb_half1, 16) + dechex(pointb_half2, 16)
    pointb_prefix = gmpy2.mpz(encpointb[:2], 16) ^ (gmpy2.mpz(scrypthash[126:], 16) & 1)
    pointb = dechex(pointb_prefix, 1) + pointb_xcoord
    newkey = multiplypub(pointb, passfactor, False)

    if flagbyte in COMPRESSION_FLAGBYTES:
        newkey = compress(newkey)

    address = pubtoaddress(newkey, "00")
    addrhex = (
        hexstrlify(address)
        if isinstance(address, bytes)
        else hexstrlify(bytearray(address, "ascii"))
    )
    addresshash2 = hash256(addrhex)[:8]

    if addresshash == addresshash2:
        if outputlotsequence and lotsequence is not False:
            lotsequence = gmpy2.mpz(lotsequence, 16)
            sequence = lotsequence % 4096
            lot = (lotsequence - sequence) // 4096
            return address, lot, sequence
        else:
            return address if not outputlotsequence else (address, False, False)
    else:
        return (False, False, False) if outputlotsequence else False


def addversion(encpriv, version="80"):
    encpriv = b58d(encpriv)
    version = hexstrlify(unhexlify(version))
    assert len(version) == 2
    assert len(encpriv) == 78
    assert encpriv[:4] == "0142" or encpriv[:4] == "0143"

    if encpriv[:4] == "0142":
        newprefix = "10df"
    else:
        newprefix = "10e0"
    return b58e(newprefix + version + encpriv[4:])


def stripversion(encpriv, outputversion=False):
    encpriv = b58d(encpriv)
    assert encpriv[:3] == "10d" or encpriv[:3] == "10e"
    assert len(encpriv) == 80
    if encpriv[:3] == "10d":
        prefix = "0142"
    else:
        prefix = "0143"
    version = encpriv[4:6]
    if outputversion:
        return b58e(prefix + encpriv[6:]), version
    else:
        return b58e(prefix + encpriv[6:])
