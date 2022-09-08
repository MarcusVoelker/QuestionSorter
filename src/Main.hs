{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use infix" #-}
module Main (main) where

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.State
import Data.Char
import Data.List
import qualified Data.Map as M
import Data.Maybe
import System.Environment
import System.IO

data Comp = Less | More | None deriving (Show, Eq, Ord)

inv :: Comp -> Comp
inv Less = More
inv More = Less
inv None = None

class (Show a, Eq a, Ord a) => Data a

instance Data Int

instance Data Char

instance (Data a) => Data [a]

type SST a = M.Map (a, a) Comp

type QS a b = StateT (SST a) IO b

type QSM a b = MaybeT (StateT (SST a) IO) b

data CM a = CM (M.Map a Int) (M.Map (a, Int) Int) deriving (Show, Eq)

debugOut :: (MonadIO m) => String -> m ()
debugOut x = return () --liftIO $ putStrLn x

askComp :: (Data a) => a -> a -> QS a Comp
askComp l r = do
  m <- get
  if (l, r) `M.member` m
    then return (m M.! (l, r))
    else do
      res <- liftIO $ do
        putStr $ "Comparing (1) '" ++ show l ++ "' and (2) '" ++ show r ++ "'? "
        hFlush stdout
        resp <- getLine
        let val
              | resp == "1" = More
              | resp == "2" = Less
              | otherwise = None
        return val
      modify (M.insert (l, r) res)
      modify (M.insert (r, l) (inv res))
      return res

unmon3 :: (Monad m) => (a, b, m c) -> m (a, b, c)
unmon3 (a, b, c) = do
  c' <- c
  return (a, b, c')

findFirst :: (Monad m) => (a -> Bool) -> [m a] -> MaybeT m a
findFirst _ [] = fail ""
findFirst p (x : xs) = do
  r <- lift x
  if p r then return r else findFirst p xs

dislodge1 :: (Data a) => [[a]] -> QSM a ([[a]], (a, a))
dislodge1 c = do
  debugOut $ "Finding Dislodging for " ++ show c
  let ls = [unmon3 (i, j, askComp (head (c !! i)) (head (c !! j))) | i <- [0 .. length c - 1], j <- [i + 1 .. length c - 1]]
  (vl, vr, cr) <- findFirst (\(_, _, r) -> r /= None) ls
  return $
    if cr == Less
      then (zipWith (\i ci -> (if i == vr then tail ci else ci)) [0 ..] c, (head (c !! vl), head (c !! vr)))
      else (zipWith (\i ci -> (if i == vl then tail ci else ci)) [0 ..] c, (head (c !! vr), head (c !! vl)))

dislodgeSeq :: (Data a) => [[a]] -> QSM a [(a, a)]
dislodgeSeq c =
  if any null c
    then return []
    else do
      (c', t) <- dislodge1 c
      (t :) <$> dislodgeSeq c'

subSeq :: (Eq a) => [[a]] -> [(a, a)] -> [(a, a)]
subSeq _ [r] = [r]
subSeq c ((xi, yi) : rs) =
  let r@((xi1, yi1) : ss) = subSeq c rs
      xc = head $ dropWhile (notElem xi1) c
   in if xi1 == head xc
        then r
        else
          let pre = fst $ head $ dropWhile ((/= xi1) . snd) $ zip xc (tail xc)
           in if yi == pre then (xi, yi) : r else r

repeel :: (Data a) => [[a]] -> (a, a) -> QSM a [[a]]
repeel c (xi, yi) = do
  debugOut $ "Repeeling " ++ show c ++ " with " ++ show (xi, yi)
  let idx = fst $ head $ filter (\(i, ci) -> elem xi ci) $ zip [0 ..] c
  let idy = fst $ head $ filter (\(i, ci) -> elem yi ci) $ zip [0 ..] c
  let new = takeWhile (/= xi) (c !! idx)
  let rest = (c !! idy) ++ dropWhile (/= xi) (c !! idx)
  let res = new : rest : (c \\ [c !! idx, c !! idy])
  debugOut $ "Repeeled to " ++ show res
  return res

peel1 :: (Data a) => [[a]] -> QSM a [[a]]
peel1 c = do
  seq <- dislodgeSeq c
  let js = subSeq c seq
  debugOut $ "Found Dislodging Sequence " ++ show js
  c' <- foldM repeel c (reverse $ tail js)
  let x1 = fst $ head js
  let y1 = snd $ head js
  let idx = fst $ head $ filter (\(i, ci) -> elem x1 ci) $ zip [0 ..] c'
  let idy = fst $ head $ filter (\(i, ci) -> elem y1 ci) $ zip [0 ..] c'
  let res = (c' !! idy ++ c' !! idx) : (c' \\ [c' !! idx, c' !! idy])
  debugOut $ "Dislodged to " ++ show res
  return res

peeling :: (Data a) => Int -> [[a]] -> QSM a [[a]]
peeling w c
  | length c <= w = return c
  | otherwise = do
    p <- peel1 c
    peeling w p

mergesortWRec :: (Data a) => Int -> [a] -> QSM a [[a]]
mergesortWRec w p
  | length p <= w = return $ map return p
  | otherwise = do
    debugOut $ "Mergesorting " ++ show p
    let (p1, p2) = splitAt (div (length p) 2) p
    c1 <- mergesortWRec w p1
    c2 <- mergesortWRec w p2
    debugOut $ "Peeling " ++ show (c1 ++ c2)
    r <- peeling w (c1 ++ c2)
    debugOut $ "Peeled to " ++ show r
    return r

mergesortW :: (Data a) => Int -> [a] -> QSM a (CM a)
mergesortW w p = do
  c <- mergesortWRec w p
  lift $ chainMerge c

mergesortRec :: (Data a) => Int -> [a] -> QS a (CM a)
mergesortRec i p = do
  debugOut ("Attempting Merge with w <= " ++ show i)
  cur <- runMaybeT (mergesortW i p)
  maybe (mergesortRec (2 * i) p) return cur

mergesort :: (Data a) => [a] -> QS a (CM a)
mergesort = mergesortRec 1

idxes :: (Data a) => M.Map a Int -> [a] -> (Int, Int, [a]) -> QS a [((a, Int), Int)]
idxes _ [] _ = return []
idxes _ ci (j, lj, []) = return $ map (\x -> ((x, j), lj)) ci
idxes idx (x : ci) (j, lj, y : cj) = do
  cmp <- askComp x y
  case cmp of
    More -> (((x, j), idx M.! y) :) <$> idxes idx ci (j, lj, y : cj)
    _ -> idxes idx (x : ci) (j, lj, cj)

chainMerge :: (Data a) => [[a]] -> QS a (CM a)
chainMerge c = do
  let selfIdx = M.fromList $ concatMap (\ci -> zip ci [0 ..]) c
  let idxC = zip [0 ..] c
  let inChain = M.fromList $ concatMap (\(i, ci) -> map (,i) ci) idxC
  qs <- M.fromList . concat <$> sequence [idxes selfIdx (c !! i) (j, length (c !! j), c !! j) | i <- [0 .. length c - 1], j <- [0 .. length c - 1], i /= j]
  let mp = M.union qs $ M.fromList $ map (\(x, d) -> ((x, inChain M.! x), d)) $ M.toList selfIdx
  return $ CM inChain mp

runThing :: (Data a, Show b) => QS a b -> IO ()
runThing qs = evalStateT qs M.empty >>= print

nodeName :: String -> String
nodeName = map toLower . filter isAlpha

calcEdges :: CM String -> [(String, String)]
calcEdges (CM cs rels) =
  let names = map fst $ M.toList cs
      chains = M.fromList $ map (\n -> let c = cs M.! n in ((c, rels M.! (n, c)), n)) names
   in concatMap
        ( \((name, idx), h) ->
            if idx == cs M.! name
              then [(name, chains M.! (idx, h + 1)) | M.member (idx, h + 1) chains]
              else [(name, chains M.! (idx, h)) | M.member (idx, h) chains]
        )
        $ M.toList rels

dotRes :: CM String -> IO ()
dotRes (CM cs rels) = do
  let names = map fst $ M.toList cs
  putStrLn "digraph G {"
  mapM_ (\name -> putStrLn ("  " ++ nodeName name ++ "[label=\"" ++ name ++ "\"]")) names
  mapM_
    (\(a, b) -> putStrLn $ "  " ++ nodeName a ++ " -> " ++ nodeName b)
    $ calcEdges (CM cs rels)
  putStrLn "}"

main :: IO ()
main = do
  as <- getArgs
  if null as
    then putStrLn "Missing Argument!"
    else do
      list <- readFile (head as)
      evalStateT (mergesort $ lines list) M.empty >>= dotRes