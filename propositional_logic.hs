#! /usr/bin/runhaskell

module PropositionalLogic where

import System.Console.Readline
import Data.Char
import Control.Monad
import System.Console.ANSI

data Proposition = P Int
                   | Q Int
                   | R Int
                   | Conditional Proposition Proposition
                   | Negation Proposition
                   | Invalid
    deriving (Eq)

instance Show Proposition where
    show (P 0) = "p"
    show (Q 0) = "q"
    show (R 0) = "r"
    show (P n) = "p_" ++ show n
    show (Q n) = "q_" ++ show n
    show (R n) = "r_" ++ show n
    show (Conditional p q) = "(" ++ show p ++ " => " ++ show q ++ ")"
    show (Negation p) = "~" ++ show p
    show Invalid = "#"

(~>) :: Proposition -> Proposition -> Proposition
p ~> q = Conditional p q
n :: Proposition -> Proposition
n p = Negation p

infixr 1 ~>

p :: Proposition
p = (P 0)
q :: Proposition
q = (Q 0)
r :: Proposition
r = (R 0)

modusPonens :: Proposition -> Proposition -> Proposition
modusPonens p (Conditional q r)
    | p == q    = r
    | otherwise = Invalid
modusPonens _ _ = Invalid

axiom1 :: Proposition -> Proposition -> Proposition
axiom1 p q = p ~> q ~> p

axiom2 :: Proposition -> Proposition -> Proposition -> Proposition
axiom2 p q r = (p ~> q ~> r) ~> (p ~> q) ~> p ~> r

axiom3 :: Proposition -> Proposition -> Proposition
axiom3 p q = ((n p) ~> (n q)) ~> ((n p) ~> q) ~> p

substitute :: Proposition -> Proposition -> Proposition -> Proposition
substitute old new (Negation whole) = Negation (substitute old new whole)
substitute old new (Conditional antecedent consequent) = Conditional (substitute old new antecedent) (substitute old new consequent)
substitute old new whole
    | whole == old    = new
    | otherwise       = whole

data Token = TokP Int | TokQ Int | TokR Int | TokCond | TokNeg | TokRParen | TokLParen | TokError
    deriving (Eq, Show)

tokenize :: String -> [Token]
tokenize []               = []
tokenize (' ':xs)         = tokenize xs
tokenize ('~':[])         = [TokError]
tokenize ('~':')':_)      = [TokError]
tokenize ('~':'=':_)      = [TokError]
tokenize ('~':xs)         = TokNeg:(tokenize xs)
tokenize ('=':'>':')':_)  = [TokError]
tokenize ('=':'>':[])     = [TokError]
tokenize ('=':'>':xs)     = TokCond:(tokenize xs)
tokenize ('(':')':_)      = [TokError]
tokenize ('(':[])         = [TokError]
tokenize ('(':'=':_)      = [TokError]
tokenize ('(':xs)         = TokLParen:(tokenize xs)
tokenize (')':'(':_)      = [TokError]
tokenize (')':'~':_)      = [TokError]
tokenize (')':'p':_)      = [TokError]
tokenize (')':'q':_)      = [TokError]
tokenize (')':'r':_)      = [TokError]
tokenize (')':xs)         = TokRParen:(tokenize xs)
tokenize ['p']            = [TokP 0]
tokenize ['q']            = [TokQ 0]
tokenize ['r']            = [TokR 0]
tokenize (x:'_':[])       = [TokError]
tokenize (x:y:xs)
    | elem x "pqr" && elem y "=) " = (prop 0):(tokenize (y:xs))
    | elem x "pqr" && y == '_' =
        if xs == []
            then [TokError]
            else if isDigit (head xs)
                then (prop (read atom)):(tokenize nonatom)
                else [TokError]
    | otherwise                        = [TokError]
    where
        prop :: Int -> Token
        prop
            | x == 'p'    = TokP
            | x == 'q'    = TokQ
            | x == 'r'    = TokR
        (atom, nonatom)
            | elem y "=) "    = ("0", y:xs)
            | y == '_'        = splitAtom xs
        splitAtom :: String -> (String, String)
        splitAtom [] = ([], [])
        splitAtom (z:zs)
            | isDigit z    = (z:(fst (splitAtom zs)), (snd (splitAtom zs)))
            | otherwise      = ([], z:zs)
tokenize _ = [TokError]

containsTokError :: [Token] -> Bool
containsTokError = elem TokError

splitSentences :: [Token] -> ([Token], [Token])
splitSentences [] = ([], [])
splitSentences (TokNeg:xs) = (TokNeg:(fst (splitSentences xs)), snd (splitSentences xs))
splitSentences ((TokP n):xs) = ([TokP n], xs)
splitSentences ((TokQ n):xs) = ([TokQ n], xs)
splitSentences ((TokR n):xs) = ([TokR n], xs)
splitSentences (TokLParen:xs) = parenParse 1 xs
    where
        parenParse :: Int -> [Token] -> ([Token], [Token])
        parenParse _ [] = ([], [])
        parenParse 1 (TokRParen:ys) = ([], ys)
        parenParse n (TokRParen:ys) = (TokRParen:(fst (parenParse (n-1) ys)), snd (parenParse (n-1) ys))
        parenParse n (TokLParen:ys) = (TokLParen:(fst (parenParse (n+1) ys)), snd (parenParse (n+1) ys))

parse' :: [Token] -> Proposition
parse' (TokNeg:xs)
    | containsTokError xs       = Invalid
    | second == []              = Negation $ parse' first
    | head second == TokCond    = (Conditional (Negation $ parse' first) (parse' $ tail second))
    | otherwise                 = Invalid
    where
        (first, second) = splitSentences xs
parse' [TokP n] = P n
parse' [TokQ n] = Q n
parse' [TokR n] = R n
parse' xs
    | containsTokError xs       = Invalid
    | second == []              = parse' first
    | head second == TokCond    = Conditional (parse' first) (parse' (tail second))
    | otherwise                 = Invalid
    where
        (first, second) = splitSentences xs

parse :: String -> Proposition
parse = parse'.tokenize

data ProofCommand = ModusPonens Int Int | Axiom1 Proposition Proposition | Axiom2 Proposition Proposition Proposition | Axiom3 Proposition Proposition | SubProof Proposition | Assumption Proposition | Substitute Int Proposition Proposition | Failure
    deriving (Eq, Show)

proof' :: [Proposition] -> [ProofCommand] -> IO ()
proof' xs ys = do
                putStrLn opening
                writeProof xs ys
                proposition <- getCommand True
                if (commandToProposition xs proposition) == Invalid
                    then proof' xs ys
                    else proof' (xs ++ [(commandToProposition xs proposition)]) (ys ++ [proposition])

commandToProposition :: [Proposition] -> ProofCommand -> Proposition
commandToProposition xs (ModusPonens m n)
    | inRange xs m && inRange xs n    = modusPonens (xs!!m) (xs!!n)
    | otherwise                       = Invalid
commandToProposition _ (Axiom1 p q) = axiom1 p q
commandToProposition _ (Axiom2 p q r) = axiom2 p q r
commandToProposition _ (Axiom3 p q ) = axiom3 p q

printJustification :: ProofCommand -> String
printJustification (ModusPonens m n) = show m ++ ", " ++ show n ++ ", "  ++ "MP"
printJustification (Axiom1 _ _) = "Axioms I"
printJustification (Axiom2 _ _ _) = "Axioms II"
printJustification (Axiom3 _ _) = "Axioms III"

inRange :: [a] -> Int -> Bool
inRange xs n = n >= 0 && n < length xs

proof :: IO ()
proof = do
            writeProof [] []
            clearFromCursorToScreenBeginning
            setCursorPosition 0 0
            proof' [] []

opening :: String
opening = "The Proof Is In The Pudding\n------------------"

writeProof :: [Proposition] -> [ProofCommand] -> IO ()
writeProof xs ys = do
                 clearFromCursorToScreenBeginning
                 setCursorPosition 0 0
                 mapM_ putStrLn (opening : lines)
    where
        lines = zipWith3 (\x y z -> show y ++ ". (" ++ printJustification z ++ ")\t" ++ show x) xs [1 .. ] ys

getCommand :: Bool -> IO ProofCommand
getCommand printout = do
                 printCommands printout
                 option <- liftAssertion (readline "\n:: Choose an option:\n")
                 parseOption option
             where
                 parseOption :: String -> IO ProofCommand
                 parseOption option =
                       case filter (/= ' ') option of
                           ("I") -> getAxiom1
                           ("II") -> getAxiom2
                           ("III") -> getAxiom3
                           ("MP") -> getModusPonens
--                           ("SUB") -> getSubstitution
                           _ -> do
                                 putStr "Invalid option. Try again.\n"
                                 getCommand False
                 getAxiom1 = do
                              putStrLn "Axioms I :: P => (Q => P)"
                              p <- liftAssertion (readline "Enter P:\n")
                              if parse p == Invalid
                                 then do
                                       putStrLn "Not a valid formula. Try again."
                                       getAxiom1
                                 else do
                                       q <- liftAssertion (readline "Enter Q:\n")
                                       if parse q == Invalid
                                           then do
                                                 putStrLn "Not a valid formula. Try again."
                                                 getAxiom1
                                            else return (Axiom1 (parse p) (parse q))
                                      
                 getAxiom2 = do
                              putStrLn "Axioms II :: (P => (Q => R)) => ((P => Q) => (P => R))"
                              p <- liftAssertion (readline "Enter P:\n")
                              if parse p == Invalid
                                 then do
                                       putStrLn "Not a valid formula. Try again."
                                       getAxiom2
                                 else do
                                       q <- liftAssertion (readline "Enter Q:\n")
                                       if parse q == Invalid
                                           then do
                                                 putStrLn "Not a valid formula. Try again."
                                                 getAxiom2
                                           else do
                                                 r <- liftAssertion (readline "Enter R:\n")
                                                 if parse r == Invalid
                                                     then do
                                                           putStrLn "Not a valid formula. Try again."
                                                           getAxiom2
                                                     else return (Axiom2 (parse p) (parse q) (parse r))
                 getAxiom3 = do
                              putStrLn "Axioms III :: (~P => ~Q) => ((~P => Q) => P)"
                              p <- liftAssertion (readline "Enter P:\n")
                              if parse p == Invalid
                                 then do
                                       putStrLn "Not a valid formula. Try again."
                                       getAxiom3
                                 else do
                                       q <- liftAssertion (readline "Enter Q:\n")
                                       if parse q == Invalid
                                           then do
                                                 putStrLn "Not a valid formula. Try again."
                                                 getAxiom3
                                           else return (Axiom3 (parse p) (parse q))

                 getModusPonens = do
                                   line1 <- liftAssertion (readline ("Enter a line number: "))
                                   if True
                                       then do
                                             line2 <- liftAssertion (readline ("Enter a line number: "))
                                             if True
                                                 then return (ModusPonens ((read line1) - 1) ((read line2) - 1))
                                                 else getModusPonens
                                       else getModusPonens
                                                 

printCommands :: Bool -> IO ()
printCommands on = if not on
                       then return ()
                       else do
                             putStrLn "---"
                             mapM_ putStrLn ["| I. Axioms I    \tII. Axioms II", "| III. Axioms III\tMP. Modus Ponens", "| SUB. Substitution"]             
                             putStrLn "---"

assertion :: Maybe [a] -> [a]
assertion (Just a) = a
assertion Nothing = []

liftAssertion :: (Monad m) => m (Maybe [a]) -> m [a]
liftAssertion = liftM assertion

main :: IO ()
main = proof
