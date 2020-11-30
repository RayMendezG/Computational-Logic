module Practica02

where

import Data.List as L

--Ejercicio 1, definimos las formulas de PL ---

type Variable = String
data PLvar v =
          Bot                       -- Constructor para bottom
        | Top                       -- Constructor para top
        | Var v                     -- Constructor de variables
        | Imp (PLvar v) (PLvar v)   -- Constructor de implicaciones
        | Dis (PLvar v) (PLvar v)   -- Constructor de disyunciones
        | Con (PLvar v) (PLvar v)   -- Constructor de conjunciones
        | Nand (PLvar v) (PLvar v)  -- Constructor de Nand
        | Neg (PLvar v)             -- Constructor de negaciones
        deriving (Eq,Show)
--

type PL= PLvar Variable  
type Valuacion = Variable -> Int --Asignar un entero a una Variable
type Modelo = [Variable] -- Crear un modelo apartir de Variables


-- Si phi en PL es una disyunción de literales,
-- entonces disLit2ListLit transforma phi en una lista de literales.
--Ejemplos: (x3 | !x4) --> [x3,!x4], Bot ---> []
disLit2ListLit :: PL -> [PL]
disLit2ListLit phi = case phi of
    Bot         -> []
    Top         -> []
    Var x       -> [Var x]
    Neg (Var x) -> [Neg (Var x)]
    (Con alpha beta) -> (disLit2ListLit (Neg(alpha))) ++ (disLit2ListLit (Neg(beta))) --Se realiza un equivalencia lógica para la conjunción
    (Dis alpha beta) -> (disLit2ListLit alpha) ++ (disLit2ListLit beta)
    (Imp alpha beta) -> ((disLit2ListLit (Neg(alpha)))) ++ (disLit2ListLit beta)
    
-- Tests
--    
-- disLit2ListLit (Imp (Var "p") (Var "q"))    
-- disLit2ListLit (Neg(Var "p"))
-- disLit2ListLit (Con (Neg(Var "p")) (Neg(Var "q")))
-- disLit2ListLit (Dis (Var "p") (Var "q"))


-- Dado un literal l en PL, litComp calcula el literal complementario de l.
litComp :: PL -> PL
litComp phi = case phi of
    Top          -> Bot
    Bot          -> Top
    Var x        -> Neg (Var x)
    Neg (Var x)  -> Var x
    Con alpha beta -> (litComp alpha) `Con` (litComp beta)
    Dis alpha beta -> (litComp alpha) `Dis` (litComp beta)
    Imp alpha beta -> (Neg(litComp alpha)) `Dis` (litComp beta)
    _ -> error $ "litComp: phi no es literal, phi="++(show phi)

-- Tests
--
-- litComp (Neg(Var "p"))
-- litComp (Imp (Var "p") (Neg(Var "q")))
-- litComp (Con (Neg(Var "p")) (Neg(Var "q")))
-- litComp (Dis (Var "p") (Var "q"))


-- Dada una clausula de PL, representada por una lista de literales ll,
-- clausulaVAL determina si ll es una clausula valida.
-- ll es valida sii ll tiene al menos dos literales complementarios.
clausulaVal :: [PL] -> Bool
clausulaVal ll = case ll of
    []      -> False
    (l:ls)  -> (litComp l) `elem` ll || clausulaVal ls

-- Tests
--
-- clausulaVal [(Var "p"), (Neg(Var "p"))]
-- clausulaVal [(Var "p"), (Neg(Var "q"))]
-- clausulaVal [(Var "p"), (Neg(Var "p")), (Var "q")]                    
      

-- Dada phi en PL, cnf2LListLit transforma phi a una formula phi' en CNF,
-- donde phi' esta representada como una lista de listas de literales.
--Ejemplos: (x1 | x2) & (x3 | !x4) ---> [[x1,x2], [x3,!x4]], Top ---> []
cnf2LListLit :: PL -> [[PL]]
cnf2LListLit phi = case phi of
    Top              -> []
    Bot              -> []
    Var x       -> [[Var x]]
    Neg (Var x) -> [[Neg (Var x)]]
    (Dis alpha beta) -> [disLit2ListLit phi]
    (Con alpha beta) -> (cnf2LListLit alpha) ++ (cnf2LListLit beta)
    (Imp alpha beta) -> [disLit2ListLit phi]
    _                -> error $ "cnf2LListLit: phi no esta en CNF, phi="++(show phi)

-- Tests 
--
-- cnf2LListLit (Con (Dis (Var "p") (Var "q")) (Dis (Var "r") (Neg(Var "s"))))
-- cnf2LListLit (Imp (Var "p") (Neg(Var "q")))


-- Dada phi en CNF, representada como una lista de listas de literales lc,
-- clauListTrue determina si todas las clausulas de lc son validas.
-- Es decir clauListTrue determina si todos los elementos de lc son clausulas validas.
clauListVal :: [[PL]] -> Bool
clauListVal lc = case lc of
    []     -> True
    (c:cs) -> clausulaVal c && clauListVal cs
                    
-- Tests
--
-- clauListVal [[Var "p"],[Neg (Var "p")]]
-- clauListVal [[Var "q", Neg(Var "q")],[Neg(Var "p"), Var "p"]]                 


-- Dada phi en PL, decide si phi pertenece, o no, a VAL:={phi in PL | forall m: m |= phi}.
-- Esto se hace transformando primero phi a una formula en CNF representada mediante una lista de listas de literales,
-- y luego aplicando clauListVal a dicha lista.
decideCNFenVAL :: PL -> Bool
decideCNFenVAL phi = clauListVal (cnf2LListLit phi)

--Tests
--
-- decideCNFenVAL (Imp (Var "p") (Var "p"))
-- decideCNFenVAL (Con (Var "p") (Var "q"))
-- decideCNFenVAL (Dis (Var "p") (Var "q"))    
-- decideCNFenVAL (Dis (Dis(Var "p")(Var "q")) (Dis(Var "r")(Var "s")))


-- Dada phi en PL, decide si phi es satisfactible, es decir que exista sigma |= phi,
--para esto necesitamos que no existan terminos complementarios, lo que hicimos fue negar 
--el resultado de "decideCNFenVAL" que determina si hay terminos complementarios. 
decideDNFenSAT :: PL -> Bool
decideDNFenSAT phi = not (clauListVal (cnf2LListLit phi))

-- Tests:
-- decideDNFenSAT (Imp (Var "p") (Var "q"))
-- decideDNFenSAT (Imp (Var "p") (Var "p"))    
-- decideDNFenSAT (Con (Var "p") (Var "q"))
-- decideDNFenSAT (Dis (Var "p") (Var "q"))    
-- decideDNFenSAT (Dis (Dis(Var "p")(Var "q")) (Dis(Var "r")(Var "s")))










