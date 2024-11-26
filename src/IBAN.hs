--
-- INFOB3CC Concurrency
-- Practical 1: IBAN calculator
--
-- http://ics.uu.nl/docs/vakken/b3cc/assessment.html
--
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use if" #-}
module IBAN (

  Mode(..), Config(..),
  count, list, search

) where

import Control.Concurrent
import Crypto.Hash.SHA1
import Data.Atomics                                       ( readForCAS, casIORef, peekTicket, Ticket )
import Data.IORef
import Data.List                                          ( elemIndex )
import Data.Word
import Data.Maybe                                         ( fromJust )
import System.Environment
import System.IO
import Data.ByteString.Char8                              ( ByteString )
import qualified Data.ByteString                          as B
import qualified Data.ByteString.Char8                    as B8


-- -----------------------------------------------------------------------------
-- 0. m-test
-- -----------------------------------------------------------------------------

-- Perform the m-test on 'number'. Use `div` and `mod` to extract digits from
-- the number; do not use `show`, as it is too slow.
mtest :: Int -> Int -> Bool
mtest m number =
  -- Implement the m-test here!
  calculateNumber number 1 `mod` m == 0
  where
    calculateNumber :: Int -> Int -> Int
    calculateNumber 0 _ = 0
    calculateNumber number count = (number `rem` 10) * count + calculateNumber (number `quot` 10) (count + 1)


-- -----------------------------------------------------------------------------
-- 1. Counting mode (3pt)
-- -----------------------------------------------------------------------------

count :: Config -> IO Int
count config = do
  -- Implement count mode here!
  sharedCount <- newIORef 0
  forkThreads (cfgThreads config) (countThread config sharedCount)
  readIORef sharedCount

--Managing threads
countThread :: Config -> IORef Int -> Int -> IO ()
countThread config sharedCount threadID = do
  let ranges = divideRange (cfgThreads config) (cfgLower config) (cfgUpper config)
  let (lower, upper) = ranges !! threadID
  if threadID > length ranges - 1
    then return ()
  else do
    let new = countRange (cfgModulus config) lower upper
    old <- readForCAS sharedCount
    evaluate new
    writeToRef sharedCount old new

writeToRef :: IORef Int -> Ticket Int -> Int -> IO ()
writeToRef sharedCount old new = do
  (switched, newTicket) <- casIORef sharedCount old (peekTicket old + new)
  case switched of
    False -> writeToRef sharedCount newTicket new
    True  -> return ()

--Computing the number of valid accounts
countRange :: Int -> Int -> Int -> Int
countRange m lower upper  | lower == upper  = 0
                          | otherwise       = case mtest m lower of
                            True  -> 1 + countRange m (lower + 1) upper
                            False -> countRange m (lower + 1) upper

divideRange :: Int -> Int -> Int -> [(Int, Int)]
divideRange t lower upper | lower == upper  = []
                          | otherwise       = case range `mod` t == 0 of
                            True  -> (lower, newLowerDivisible) : divideRange (t-1) newLowerDivisible upper
                            False -> (lower, newLowerNotDivisible) : divideRange (t-1) newLowerNotDivisible upper
  where
    range = upper - lower
    newLowerDivisible = lower + (range `div` t)
    newLowerNotDivisible = lower + (range `div` t) + 1

-- -----------------------------------------------------------------------------
-- 2. List mode (3pt)
-- -----------------------------------------------------------------------------

list :: Handle -> Config -> IO ()
list handle config = do
  -- Implement list mode here!
  -- Remember to use "hPutStrLn handle" to write your output.
  sharedSequence <- newMVar 1
  forkThreads (cfgThreads config) (listThread config handle sharedSequence)

listThread :: Config -> Handle -> MVar Int -> Int -> IO ()
listThread config handle sharedSequence threadID = do
  let ranges = divideRange (cfgThreads config) (cfgLower config) (cfgUpper config)
  let (lower, upper) = ranges !! threadID
  if threadID > length ranges - 1
    then return ()
  else do
    listRange handle sharedSequence (cfgModulus config) lower upper

listRange :: Handle -> MVar Int -> Int -> Int -> Int -> IO ()
listRange handle sharedSequence m lower upper | lower == upper  = return ()
                                              | otherwise       = if mtest m lower
                                                  then do 
                                                    outputAccount handle sharedSequence lower
                                                    listRange handle sharedSequence m (lower + 1) upper
                                                else 
                                                  listRange handle sharedSequence m (lower + 1) upper

outputAccount :: Handle -> MVar Int -> Int -> IO ()
outputAccount handle sharedSequence account = do
  seq' <- takeMVar sharedSequence
  hPutStrLn handle (show seq' ++ " " ++ show account)
  putMVar sharedSequence (seq' + 1)

-- -----------------------------------------------------------------------------
-- 3. Search mode (4pt)
-- -----------------------------------------------------------------------------

data Queue a = Queue (MVar (List a)) (MVar (List a))
type List a = MVar (Item a)
data Item a = Item a (List a)

newQueue :: IO (Queue a)
newQueue = do
  hole <- newEmptyMVar
  readLock <- newMVar hole
  writeLock <- newMVar hole
  return $ Queue readLock writeLock

enqueue :: Queue a -> a -> IO ()
enqueue (Queue _ writeLock) val = do
  newHole <- newEmptyMVar
  oldHole <- takeMVar writeLock
  let item = Item val newHole
  putMVar oldHole item
  putMVar writeLock newHole

dequeue :: Queue a -> IO a
dequeue (Queue readLock _) = do
  readEnd <- takeMVar readLock
  (Item value rest) <- takeMVar readEnd
  putMVar readLock rest
  return value

search :: Config -> ByteString -> IO (Maybe Int)
search config query = do
  -- Implement search mode here!
  undefined

findAccount :: ByteString -> Int -> Int -> Int -> Maybe Int
findAccount query m lower upper | lower == upper    = Nothing
                                | otherwise         = 
                                  if mtest m lower then
                                    if checkHash query (show lower) then
                                      Just lower
                                    else
                                      findAccount query m (lower + 1) upper
                                  else
                                    findAccount query m (lower + 1) upper


-- -----------------------------------------------------------------------------
-- Starting framework
-- -----------------------------------------------------------------------------

data Mode = Count | List | Search ByteString
  deriving Show

data Config = Config
  { cfgLower   :: !Int
  , cfgUpper   :: !Int
  , cfgModulus :: !Int
  , cfgThreads :: !Int
  }
  deriving Show

-- Evaluates a term, before continuing with the next IO operation.
--
evaluate :: a -> IO ()
evaluate x = x `seq` return ()

-- Forks 'n' threads. Waits until those threads have finished. Each thread
-- runs the supplied function given its thread ID in the range [0..n).
--
forkThreads :: Int -> (Int -> IO ()) -> IO ()
forkThreads n work = do
  -- Fork the threads and create a list of the MVars which
  -- per thread tell whether the work has finished.
  finishVars <- mapM work' [0 .. n - 1]
  -- Wait on all MVars
  mapM_ takeMVar finishVars
  where
    work' :: Int -> IO (MVar ())
    work' index = do
      var <- newEmptyMVar
      _   <- forkOn index (work index >> putMVar var ())
      return var

-- Checks whether 'value' has the expected hash.
--
checkHash :: ByteString -> String -> Bool
checkHash expected value = expected == hash (B8.pack value)
