-- | This module contains fuctions and templates for building up and breaking
--   down packed bit structures. It's something like Erlang's bit-syntax (or,
--   actually, more like Python's struct module).
--
--   This code uses Data.ByteString which is included in GHC 6.5 and you can
--   get it for 6.4 at <http://www.cse.unsw.edu.au/~dons/fps.html>
module Data.BitSyntax (
  -- * Building bit structures
  -- | The core function here is makeBits, which is a perfectly normal function.
  --   Here's an example which makes a SOCKS4a request header:
  -- @
  --   makeBits [U8 4, U8 1, U16 80, U32 10, NullTerminated \"username\",
  --             NullTerminated \"www.haskell.org\"]
  -- @
  BitBlock(..),
  makeBits,
  -- * Breaking up bit structures
  -- | The main function for this is bitSyn, which is a template function and
  --   so you'll need to run with @-fth@ to enable template haskell
  --   <http://www.haskell.org/th/>.
  --
  --   To expand the function you use the splice command:
  -- @
  --   $(bitSyn [...])
  -- @
  --
  -- The expanded function has type @ByteString -> (...)@ where the elements of
  -- the tuple depend of the argument to bitSyn (that's why it has to be a template
  -- function).
  --
  -- Heres an example, translated from the Erlang manual, which parses an IP header:
  --
  -- @
  -- decodeOptions bs ([_, hlen], _, _, _, _, _, _, _, _, _)
  --   | hlen > 5  = return $ BS.splitAt (fromIntegral ((hlen - 5) * 4)) bs
  --   | otherwise = return (BS.empty, bs)
  -- @
  --
  -- @
  -- ipDecode = $(bitSyn [PackedBits [4, 4], Unsigned 1, Unsigned 2, Unsigned 2,
  --                      PackedBits [3, 13], Unsigned 1, Unsigned 1, Unsigned 2,
  --                      Fixed 4, Fixed 4, Context \'decodeOptions, Rest])
  -- @
  --
  -- @
  -- ipPacket = BS.pack [0x45, 0, 0, 0x34, 0xd8, 0xd2, 0x40, 0, 0x40, 0x06,
  --                     0xa0, 0xca, 0xac, 0x12, 0x68, 0x4d, 0xac, 0x18,
  --                     0x00, 0xaf]
  -- @
  --
  -- This function has several weaknesses compared to the Erlang version: The
  -- elements of the bit structure are not named in place, instead you have to
  -- do a pattern match on the resulting tuple and match up the indexes. The
  -- type system helps in this, but it's still not quite as nice.

  ReadType(..), bitSyn,

  -- I get errors if these aren't exported (Can't find interface-file
  -- declaration for Data.BitSyntax.decodeU16)
  decodeU8, decodeU16, decodeU32, decodeU16LE, decodeU32LE) where

import Language.Haskell.TH.Lib
import Language.Haskell.TH.Syntax

import qualified Data.ByteString as BS
import Data.Char (ord)
import Control.Monad
import Test.QuickCheck (Arbitrary(), arbitrary, Gen())

import Foreign

foreign import ccall unsafe "htonl" htonl :: Word32 -> Word32
foreign import ccall unsafe "htons" htons :: Word16 -> Word16

-- There's no good way to convert to little-endian. The htons functions only
-- convert to big endian and they don't have any little endian friends. So we
-- need to detect which kind of system we are on and act accordingly. We can
-- detect the type of system by seeing if htonl actaully doesn't anything (it's
-- the identity function on big-endian systems, of course). If it doesn't we're
-- on a big-endian system and so need to do the byte-swapping in Haskell because
-- the C functions are no-ops

-- | A native Haskell version of htonl for the case where we need to convert
--   to little-endian on a big-endian system
endianSwitch32 :: Word32 -> Word32
endianSwitch32 a = ((a .&. 0xff) `shiftL` 24) .|.
                   ((a .&. 0xff00) `shiftL` 8) .|.
                   ((a .&. 0xff0000) `shiftR` 8) .|.
                   (a `shiftR` 24)

-- | A native Haskell version of htons for the case where we need to convert
--   to little-endian on a big-endian system
endianSwitch16 :: Word16 -> Word16
endianSwitch16 a = ((a .&. 0xff) `shiftL` 8) .|.
                   (a `shiftR` 8)

littleEndian32 :: Word32 -> Word32
littleEndian32 a = if htonl 1 == 1
                     then endianSwitch32 a
                     else a

littleEndian16 :: Word16 -> Word16
littleEndian16 a = if htonl 1 == 1
                     then endianSwitch16 a
                     else a

data BitBlock = -- | Unsigned 8-bit int
                U8 Int |
                -- | Unsigned 16-bit int
                U16 Int |
                -- | Unsigned 32-bit int
                U32 Int |
                -- | Little-endian, unsigned 16-bit int
                U16LE Int |
                -- | Little-endian, unsigned 32-bit int
                U32LE Int |
                -- | Appends the string with a trailing NUL byte
                NullTerminated String |
                -- | Appends the string without any terminator
                RawString String |
                -- | Appends a ByteString
                RawByteString BS.ByteString |
                -- | Packs a series of bit fields together. The argument is
                --   a list of pairs where the first element is the size
                --   (in bits) and the second is the value. The sum of the
                --   sizes for a given PackBits must be a multiple of 8
                PackBits [(Int, Int)]
                deriving (Show)

-- Encodes a member of the Bits class as a series of bytes and returns the
-- ByteString of those bytes.
getBytes :: (Integral a, Bounded a, Bits a) => a -> BS.ByteString
getBytes input =
    let getByte _ 0 = []
        getByte x remaining = (fromIntegral $ (x .&. 0xff)) :
                              getByte (shiftR x 8) (remaining - 1)
        in
        if (bitSize input `mod` 8) /= 0
           then error "Input data bit size must be a multiple of 8"
           else BS.pack $ getByte input (bitSize input `div` 8)

-- Performs the work behind PackBits
packBits :: (Word8, Int, [Word8])  -- ^ The current byte, the number of bits
                                   --   used in that byte and the (reverse)
                                   --   list of produced bytes
         -> (Int, Int)  -- ^ The size (in bits) of the value, and the value
         -> (Word8, Int, [Word8])  -- See first argument
packBits (current, used, bytes) (size, value) =
  if bitsWritten < size
    then packBits (0, 0, current' : bytes) (size - bitsWritten, value)
    else if used' == 8
           then (0, 0, current' : bytes)
           else (current', used', bytes)
  where
    top = size - 1
    topOfByte = 7 - used
    aligned = value `shift` (topOfByte - top)
    newBits = (fromIntegral aligned) :: Word8
    current' = current .|. newBits
    bitsWritten = min (8 - used) size
    used' = used + bitsWritten

bits :: BitBlock -> BS.ByteString
bits (U8 v) = BS.pack [((fromIntegral v) :: Word8)]
bits (U16 v) = getBytes ((htons $ fromIntegral v) :: Word16)
bits (U32 v) = getBytes ((htonl $ fromIntegral v) :: Word32)
bits (U16LE v) = getBytes (littleEndian16 $ fromIntegral v)
bits (U32LE v) = getBytes (littleEndian32 $ fromIntegral v)
bits (NullTerminated str) = BS.pack $ (map (fromIntegral . ord) str) ++ [0]
bits (RawString str) = BS.pack $ map (fromIntegral . ord) str
bits (RawByteString bs) = bs
bits (PackBits bitspec) =
  if (sum $ map fst bitspec) `mod` 8 /= 0
    then error "Sum of sizes of a bit spec must == 0 mod 8"
    else (\(_, _, a) -> BS.pack $ reverse a) $ foldl packBits (0, 0, []) bitspec

-- | Make a binary string from the list of elements given
makeBits :: [BitBlock] -> BS.ByteString
makeBits = BS.concat . (map bits)

data ReadType = -- | An unsigned number of some number of bytes. Valid
                --   arguments are 1, 2 and 4
                Unsigned Integer |
                -- | An unsigned, little-endian integer of some number of
                --   bytes. Valid arguments are 2 and 4
                UnsignedLE Integer |
                -- | A variable length element to be decoded by a custom
                --   function. The function's name is given as the single
                --   argument and should have type
                --   @Monad m => ByteString -> m (v, ByteString)@
                Variable Name |
                -- | Skip some number of bytes
                Skip Integer |
                -- | A fixed size field, the result of which is a ByteString
                --   of that length.
                Fixed Integer |
                -- | Decode a value and ignore it (the result will not be part
                --   of the returned tuple)
                Ignore ReadType |
                -- | Like variable, but the decoding function is passed the
                --   entire result tuple so far. Thus the function whose name
                --   passed has type
                --   @Monad m => ByteString -> (...) -> m (v, ByteString)@
                Context Name |
                -- | Takes the most recent element of the result tuple and
                --   interprets it as the length of this field. Results in
                --   a ByteString
                LengthPrefixed |
                -- | Decode a series of bit fields, results in a list of
                --   Integers. Each element of the argument is the length of
                --   the bit field. The sums of the lengths must be a multiple
                --   of 8
                PackedBits [Integer] |
                -- | Results in a ByteString containing the undecoded bytes so
                --   far. Generally used at the end to return the trailing body
                --   of a structure, it can actually be used at any point in the
                --   decoding to return the trailing part at that point.
                Rest

fromBytes :: (Num a, Bits a) => [a] -> a
fromBytes input =
    let dofb accum [] = accum
        dofb accum (x:xs) = dofb ((shiftL accum 8) .|. x) xs
        in
        dofb 0 $ reverse input


-- | First byte of a 'BS.ByteString'.
decodeU8 :: BS.ByteString -> Word8
decodeU8 = fromIntegral . head . BS.unpack
-- | Convert little-endian 'BS.ByteString' to big-endian 'Word16'.
decodeU16 :: BS.ByteString -> Word16
decodeU16 = htons . fromBytes . map fromIntegral . BS.unpack
-- | Convert little-endian 'BS.ByteString' to big-endian 'Word32'.
decodeU32 :: BS.ByteString -> Word32
decodeU32 = htonl . fromBytes . map fromIntegral . BS.unpack
-- | Convert little-endian 'BS.ByteString' to little-endian 'Word16'.
decodeU16LE :: BS.ByteString -> Word16
decodeU16LE = littleEndian16 . fromBytes . map fromIntegral . BS.unpack
-- | Convert little-endian 'BS.ByteString' to little-endian 'Word32'.
decodeU32LE :: BS.ByteString -> Word32
decodeU32LE = littleEndian32 . fromBytes . map fromIntegral . BS.unpack

decodeBits :: [Integer] -> BS.ByteString -> [Integer]
decodeBits sizes bs =
  reverse values
  where
    (values, _, _) = foldl unpackBits ([], 0, BS.unpack bitdata) sizes
    bytesize = (sum sizes) `shiftR` 3
    (bitdata, _) = BS.splitAt (fromIntegral bytesize) bs

unpackBits :: ([Integer], Integer, [Word8]) -> Integer -> ([Integer], Integer, [Word8])
unpackBits state size = unpackBitsInner 0 state size

unpackBitsInner :: Integer ->
                   ([Integer], Integer, [Word8]) ->
                   Integer ->
                   ([Integer], Integer, [Word8])
unpackBitsInner _ (output, used, []) _ = (output, used, [])
unpackBitsInner val (output, used, current : input) bitsToGet =
  if bitsToGet' > 0
    then unpackBitsInner val'' (output, 0, input) bitsToGet'
    else if used' < 8
           then (val'' : output, used', current'' : input)
           else (val'' : output, 0, input)
  where
    bitsAv = 8 - used
    bitsTaken = min bitsAv bitsToGet
    val' = val `shift` (fromIntegral bitsTaken)
    current' = current `shiftR` (fromIntegral (8 - bitsTaken))
    current'' = current `shiftL` (fromIntegral bitsTaken)
    val'' = val' .|. (fromIntegral current')
    bitsToGet' = bitsToGet - bitsTaken
    used' = used + bitsTaken

readElement :: ([Stmt], Name, [Name]) -> ReadType -> Q ([Stmt], Name, [Name])

readElement (stmts, inputname, tuplenames) (Context funcname) = do
  valname <- newName "val"
  restname <- newName "rest"

  let stmt = BindS (TupP [VarP valname, VarP restname])
                   (AppE (AppE (VarE funcname)
                               (VarE inputname))
                         (TupE $ map VarE $ reverse tuplenames))

  return (stmt : stmts, restname, valname : tuplenames)

readElement (stmts, inputname, tuplenames) (Fixed n) = do
  valname <- newName "val"
  restname <- newName "rest"
  let dec1 = ValD (TupP [VarP valname, VarP restname])
                  (NormalB $ AppE (AppE (VarE 'BS.splitAt)
                                        (LitE (IntegerL n)))
                                  (VarE inputname))
                  []

  return (LetS [dec1] : stmts, restname, valname : tuplenames)

readElement state@(_, _, tuplenames) (Ignore n) = do
  (a, b, _) <- readElement state n
  return (a, b, tuplenames)

readElement (stmts, inputname, tuplenames) LengthPrefixed = do
  valname <- newName "val"
  restname <- newName "rest"

  let sourcename = head tuplenames
      dec = ValD (TupP [VarP valname, VarP restname])
                 (NormalB $ AppE (AppE (VarE 'BS.splitAt)
                                       (AppE (VarE 'fromIntegral)
                                             (VarE sourcename)))
                                 (VarE inputname))
                 []

  return (LetS [dec] : stmts, restname, valname : tuplenames)

readElement (stmts, inputname, tuplenames) (Variable funcname) = do
  valname <- newName "val"
  restname <- newName "rest"

  let stmt = BindS (TupP [VarP valname, VarP restname])
                   (AppE (VarE funcname) (VarE inputname))

  return (stmt : stmts, restname, valname : tuplenames)

readElement (stmts, inputname, tuplenames) Rest = do
  restname <- newName "rest"
  let dec = ValD (VarP restname)
                 (NormalB $ VarE inputname)
                 []
  return (LetS [dec] : stmts, inputname, restname : tuplenames)

readElement (stmts, inputname, tuplenames) (Skip n) = do
  -- Expands to something like:
  --   rest = Data.ByteString.drop n input
  restname <- newName "rest"
  let dec = ValD (VarP restname)
                 (NormalB $ AppE (AppE (VarE 'BS.drop)
                                       (LitE (IntegerL n)))
                                 (VarE inputname))
                 []
  return (LetS [dec] : stmts, restname, tuplenames)

readElement state (Unsigned size) = do
  -- Expands to something like:
  --    (aval, arest) = Data.ByteString.splitAt 1 input
  --    a = BitSyntax.decodeU8 aval
  let decodefunc = case size of
                     1 -> 'decodeU8
                     2 -> 'decodeU16
                     _ -> 'decodeU32 -- Default to 32
  decodeHelper state (VarE decodefunc) size

readElement state (UnsignedLE size) = do
  -- Expands to something like:
  --    (aval, arest) = Data.ByteString.splitAt 1 input
  --    a = BitSyntax.decodeU8LE aval
  let decodefunc = case size of
                     2 -> 'decodeU16LE
                     _ -> 'decodeU32LE -- Default to 4
  decodeHelper state (VarE decodefunc) size

readElement state (PackedBits sizes) =
  if sum sizes `mod` 8 /= 0
    then error "Sizes of packed bits must == 0 mod 8"
    else decodeHelper state
                      (AppE (VarE 'decodeBits)
                            (ListE $ map (LitE . IntegerL) sizes))
                      ((sum sizes) `shiftR` 3)

decodeHelper :: ([Stmt], Name, [Name])      -> Exp
                                            -> Integer
                                            -> Q ([Stmt], Name, [Name])
decodeHelper (stmts, inputname, tuplenames) decodefunc size = do
  valname <- newName "val"
  restname <- newName "rest"
  tuplename <- newName "tup"
  let dec1 = ValD (TupP [VarP valname, VarP restname])
                  (NormalB $ AppE (AppE (VarE 'BS.splitAt)
                                        (LitE (IntegerL size)))
                                  (VarE inputname))
                  []
  let dec2 = ValD (VarP tuplename)
                  (NormalB $ AppE decodefunc (VarE valname))
                  []

  return (LetS [dec1, dec2] : stmts, restname, tuplename : tuplenames)

decGetName :: Dec -> Name
decGetName (ValD (VarP name) _ _) = name
decGetName _                      = undefined -- Error!

-- | Example usage:
--
-- > parsePascalString :: Monad m => ByteString -> m (Word16, ByteString)
-- > parsePascalString bs = $( bitSyn [UnsignedLE 2, LengthPrefixed] ) bs
bitSyn :: [ReadType] -> Q Exp
bitSyn elements = do
    inputname <- newName "input"
    (stmts, restname, tuplenames) <- foldM readElement ([], inputname, []) elements
    returnS <- NoBindS `liftM` [| return $(tupE . map varE $ reverse tuplenames) |]
    return $ LamE [VarP inputname] (DoE . reverse $ returnS : stmts)


-- Tests
prop_bitPacking :: [(Int, Int)] -> Bool
prop_bitPacking fields =
  prevalues == (map fromIntegral postvalues) ||
  any (< 1) (map fst fields) ||
  any (< 0) (map snd fields)
  where
    undershoot = sum (map fst fields) `mod` 8
    fields' = if undershoot > 0
                then (8 - undershoot, 1) : fields
                else fields
    prevalues = map snd fields'
    packed = bits $ PackBits fields'
    postvalues = decodeBits (map (fromIntegral . fst) fields') packed

#if !MIN_VERSION_QuickCheck(2,1,2)
instance Arbitrary Word16 where
  arbitrary = (arbitrary :: Gen Int) >>= return . fromIntegral
instance Arbitrary Word32 where
  arbitrary = (arbitrary :: Gen Int) >>= return . fromIntegral
#endif

-- | This only works on little-endian machines as it checks that the foreign
--   functions (htonl and htons) match the native ones
prop_nativeByteShuffle32 :: Word32 -> Bool
prop_nativeByteShuffle32 x = endianSwitch32 x == htonl x
prop_nativeByteShuffle16 :: Word16 -> Bool
prop_nativeByteShuffle16 x = endianSwitch16 x == htons x
prop_littleEndian16 :: Word16 -> Bool
prop_littleEndian16 x = littleEndian16 x == x
prop_littleEndian32 :: Word32 -> Bool
prop_littleEndian32 x = littleEndian32 x == x
