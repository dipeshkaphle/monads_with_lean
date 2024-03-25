import Lean

namespace Experiment

inductive Term where
  | con : Int → Term
  | div : Term → Term → Term
deriving Repr

abbrev M (α: Type) := String × α


def unit ( a: α ) : M α :=
  ("", a)


def bind' ( m: M α ) ( k: α → M β ) : M β :=
  let (x, a) := m
  let ( y, b ) := k a
  (x.append y, b)

def out ( x: String ): M Unit :=
  (x, ())

def line (t: Term) (a: Int) :=
   "eval (" ++ reprStr t   ++ ") <== "  ++ reprStr a ++  "\n"

def eval : Term → M Int
  | Term.con x => bind' ( out (line (Term.con x) x) ) (λ _ =>  unit x )
  | Term.div x y =>
    let a := eval x
    let b := eval y
    let aByB := bind' a (λ a =>
                bind' b (λ b =>
                unit (Int.div a b)))
    let calcs := bind' aByB (λ aByB =>
              (out (line (Term.div x y) aByB)))
    bind' aByB (λ aByB =>
                bind' calcs (λ () =>
                unit aByB))

#eval eval (Term.div (Term.con 2) ( Term.con 1 ))

end Experiment

namespace Parser

-- ParserMonad "PM"
abbrev PM α := String → List (α × String)

def unit : α → PM α :=
  λ a x => [(a,x)]

private def bind' ( m: PM α ) (k: α → PM β) : PM β :=
  λ st =>
    let res := m st
    List.bind res (λ (a, s) => k a s)

instance : Monad PM where
  pure := unit
  -- M α -> (α → M β) -> M β
  bind := bind'


def item : PM Char :=
  λ ( s: String ) => match s with
    | "" => []
    | s => [(s.front, s.drop 1)]


private def twoItems : PM (Char × Char) := do
  let a <- item
  let b <- item
  pure (a,b)


#eval twoItems "monad"

def zero : PM α :=
  λ _ => []

def alternation ( m: PM α ) ( n: PM α ) : PM α :=
  λ s =>
    let m' := m s
    let n' := n s
    m' ++ n'

infix:70  " ⊗ " => alternation


private def oneOrTwoItems : PM String :=
  let one :=  item >>= λ a => pure $ String.mk [a]
  let two := item >>= λ a => item >>= λ b => pure $ String.mk [a,b]
  one ⊗ two

#eval oneOrTwoItems "monad"

def filter (p: PM α) (f: α → Bool) : PM α := do
  let a <- p
  if f a then pure a else zero

infix:70 " ▸ " => filter

def letter : PM Char :=
  filter item Char.isAlpha

def digit := do
  let dig <- filter item Char.isDigit
  pure ( dig.val - '0'.val )

def literal (c: Char) : PM Char := (filter item (λ a => a == c))

#eval ( item ▸ Char.isDigit) "123x"
#eval digit "x123x"
#eval literal 'c' "dcba"



-- Can I prove the termination property?? Seems difficult because PM is abstract
-- I guess I could actually do it by working with it's internal representation however?
-- COOL IDEA: prove termination of parser combinator in lean(work already seems to exist:
-- https://www.cse.chalmers.se/~nad/publications/danielsson-parser-combinators.pdf and
-- https://gallais.github.io/pdf/agdarsec18.pdf)
partial def iterate (m: PM α ) : PM ( List α ) :=
  let tryM := do {
    let a <- m
    let x <- iterate m
    pure (a::x)
  }
  tryM ⊗ unit []

#eval iterate digit "23 and more"

def biasedChoice (m: PM α) (n: PM α) : PM α :=
  λ s =>
    let x := m s
    if List.isEmpty x then n s else x

infix:70  " ⊕ " => biasedChoice

partial def iterate' (m: PM α) : PM (List α) :=
  let tryM := do {
    let a <- m
    let x <- iterate' m
    pure (a::x)
  }
  tryM ⊕ unit []

#eval iterate' digit "23 and more"

end Parser
