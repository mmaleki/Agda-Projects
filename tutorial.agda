{- This is a brief tutorial of Agda programming Language. -}

{- To load a file you should write "module name_of_the_file where". -}

{- To openning a file in Emacs: C-x C-f -}

module tutorial where


data Bool : Set where
  true : Bool
  false : Bool

not : Bool → Bool
not true = false
not false = true

!_ : Bool → Bool
! true = false
! false = true

{- You can also write program with unicode in Agda. For example for writing
   the set of natural number simply write "\+b+N", this gives you ℕ.
   The whole latex formula should be work in Agda.-}

{- When defining a inductive type be careful of indentation. The constructores
   should be indented. The number of space is not important. You should
   indent at least one space. But the constructore with the same level
   should be indented with the same space. -}

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

sum : ℕ → ℕ → ℕ
sum a zero = a
sum a (succ b) = succ (sum a b)



{-# BUILTIN NATURAL ℕ #-}

data Id (A : Set)(a : A ): A → Set where
  refl : Id A a a

infix 4 _≡_

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x

dneg : (b : Bool) → not (not b) ≡ b
dneg true = refl
dneg false = refl

{-
data _<_ : ℕ → ℕ → Set where
  z<n : ∀ {n : ℕ}
     ----------
    → zero < n

  s<s : ∀ {m n : ℕ}
    → m < n
     ----------
    → succ m < succ n
-}

f : ℕ → ℕ
f n = sum n 3


_∧_ : Bool → Bool → Bool
false ∧ b = false
true ∧ b = b

_∨_ : Bool → Bool → Bool
false ∨ b = b
true ∨ b = true

{- The "infix" determines the priority of an operator. Higher infix
   means higher priority. For example "not" has higher priority
   over "_∧_". The "infixl" determine the associativity from left.
   The "infixr" determine the associativity from right. -}

infix 7 not
infixl 6 _∧_
infixl 6 _∨_

{-By "Set l" agda means Set of level "l". This makes a hierarchy of types:
  "Set l" is of type "Set (l+1)". By "Set" agda means "Set 0". -}

if_then_else_ : ∀ {l} {A : Set l} → Bool → A → A → A
if true then a else b = a
if false then a else b = b

{- To evaluate a term to a normal form just C-c C-n.
   To load the whole program C-c C-l.-}

first_theorem : not (not true ) ≡ true
first_theorem = refl

second_theorem : ∀ (b : Bool) → not ( not b ) ≡ b
second_theorem true = first_theorem
second_theorem false = refl

{- To create a hole put "?" and then press C-c C-l.
   To cut a hole press C-k, and for undo cut C-y -}

third_theorem : ∀ (n m : ℕ) → (sum n m ≡ sum m n )
third_theorem = {!!}

fourth_theorem : ∀ (n : ℕ) → (sum n zero ≡ n)
fourth_theorem zero = refl
fourth_theorem (succ n') = refl


fifth_theorem : ∀ {b c} → b ∧ c ≡ true → b ≡ true
fifth_theorem {true} p = refl
fifth_theorem {false} ()

id : (A : Set) → A → A
id = \A x → x

{- Implicit argument-}

id₂ : {A : Set} → A → A
id₂ x = x


data list (A : Set) : Set where
  [] : list A
  _::_ : A → list A → list A


length : {A : Set} → list A → ℕ
length [] = 0
length (y :: y') = succ (length y')

map : {A B : Set} → (A → B) → list A → list B
map f [] = []
map f (x :: xs) = f x :: map f xs

{-The type of lists of certain length. "Vec A zero" only contains the
  nil list. The "_::_" constructore takes a natural number "n" and
  an element "x:A" and an element "xs: Vec A n" and by concating
  "x :: xs" returns a "x :: xs : Vec (succ n)" -}

data Vec (A : Set) : ℕ → Set where
  [] : Vec A 0
  _::_ : {n : ℕ} → A → Vec A n → Vec A (succ n)

head : {A : Set}{n : ℕ} → Vec A (succ n) → A
head (x :: xs) = x


{-The only way to construct an element in the image of "f" is to
  pick an argument "x" and apply "f" to "x".-}

data Image_∋_ {A B : Set}(f : A → B) : B → Set where
  im : (x : A) → Image f ∋ f x

{-Definition of the inverse operator.-}

inv : {A B : Set}(f : A → B)(y : B) → (Image f ∋ y) → A
inv f .(f x) (im x) = x

data False : Set where
record True : Set where

trivial : True
trivial = _

isTrue : Bool → Set
isTrue true = True
isTrue false = False

_<_ : ℕ → ℕ → Bool
_ < 0 = false
0 < succ n = true
succ m < succ n = m < n

k : ℕ → ℕ
k n = if (n < 5) then 0 else sum n 3

lookup : {A : Set}(xs : list A)(n : ℕ) → isTrue (n < length xs) → A
lookup [] n ()
lookup (x :: xs) 0 p = x
lookup (x :: xs) (succ n) p = lookup xs n p


data less : ℕ → ℕ → Set where
  leq-zero : {n : ℕ} → less 0 n
  leq-suc : { m n : ℕ} → less m n → less (succ m) (succ n)

trans : {l m n : ℕ} → less l m → less m n → less l n
trans leq-zero m = leq-zero
trans (leq-suc p) (leq-suc q) = leq-suc (trans p q)

{-
theorem :{n : ℕ} → less n 0 → n ≡ 0
theorem leq-zero = refl
theorem (leq-suc p) = leq-suc (theorem p)
-}

min : ℕ → ℕ → ℕ
min x y with x < y
min x y | true = x
min x y | false = y

max : ℕ → ℕ → ℕ
max x y with x < y
max x y | true = y
max x y | false = x

tail : {A : Set} → list A → list A
tail [] = []
tail ( _ :: xs) = xs

{- Proof that two numbers are equal. -}

data _≠_ : ℕ → ℕ → Set where
  z≠s : {n : ℕ} → 0 ≠ succ n
  s≠z : {n : ℕ} → succ n ≠ 0
  s≠s : {m n : ℕ} → m ≠ n → succ m ≠ succ n

data Equal? (n m : ℕ) : Set where
  eq : n ≡ m → Equal? n m
  neq : n ≠ m → Equal? n m

equal? : (n m : ℕ) → Equal? n m
equal? 0 0 = eq refl
equal? 0 (succ m) = neq z≠s
equal? (succ n) 0 = neq s≠z
equal? (succ n) (succ m) with equal? n m
equal? (succ n) (succ m) | eq refl = eq refl
equal? (succ n) (succ m) | neq p = neq (s≠s p)


{-Records -}

record Point : Set where
  field x : ℕ
        y : ℕ

makePoint : ℕ → ℕ → Point
makePoint a b = record{x = a; y = b }


record Monad (M : Set → Set) : Set1 where
  field
    return : {A : Set} → A → M A
    _>>=_  : {A B : Set} → M A → (A → M B) → M B

  mapM :{A B : Set} → (A → M B) → list A → M (list B)
  mapM f [] = return []
  mapM f (x :: xs) = f x   >>= \y →
                     mapM f xs >>= \ys →
                     return (y :: ys)

mapM' : {M : Set → Set} → Monad M →
        {A B : Set} → (A → M B) → list A → M (list B)
mapM' Mon f xs = Monad.mapM Mon f xs

module M where
  data Maybe (A : Set) : Set where
    nothing : Maybe A
    just    : A → Maybe A

  maybe_suc : Maybe ℕ → Maybe ℕ
  maybe_suc nothing = nothing
  maybe_suc (just x) = just (sum x 1)

  liftMaybe1 : {A : Set} → (A → A) → Maybe A → Maybe A
  liftMaybe1 f nothing = nothing
  liftMaybe1 f (just x) = just (f x)

  liftMaybe2 : {A : Set} → (A → A → A) → Maybe A → Maybe A → Maybe A
  liftMaybe2 f nothing _ = nothing
  liftMaybe2 f _ nothing = nothing
  liftMaybe2 f (just x) (just y) = just (f x y)

  -- nothing >>= f = nothing
  -- just x  >>= f = f x

  -- liftMaybe1 using monad operations
  -- liftMaybe1 f x = x >>= (return . f)

maybe_sum : M.Maybe ℕ → M.Maybe ℕ → M.Maybe ℕ
maybe_sum = M.liftMaybe2 sum


data _⊕_ (A B : Set) : Set where
  inl : A → A ⊕ B
  inr : B → A ⊕ B

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

proj1 : {A B : Set} → A × B → A
proj1 (x , y) = x

proj2 : {A B : Set} → A × B → B
proj2 (x , y) = y

{-Elimination rule: f:(x:A) → B ∧ a:A => f a:B[x:=a]-}

data Gender : Set where
  female : Gender
  male : Gender

data Female_name : Set where
  sara : Female_name
  avina : Female_name

data Male_name : Set where
  samiyar : Male_name
  karen : Male_name

Name : Gender → Set
Name female = Female_name
Name male = Male_name

select : (g : Gender) → Name g
select female = avina
select male = samiyar
 {-Name male = (Name g)[g := male]
   An attempt to define select such that select male is 
   not in Male_name, for example select male = avina,
   will result in a type error.
   ∀ x : A. B is true iff for all x:A there exists a proof of B.
   So a proof of ∀ x : A. B is a function which takes an x:A and
   compute an element of B. So we can identife ∀ x : A.B with 
   the dependent function set (x:A) → B. THUS...
   We just prove that ∀ g : Gender.(Name g), i.e, we just
   prove that for every gender g, (Name g) is a set of names of gender g!!! -}


{-Prove ∀ x : Bool. ~(x < x) -}

record NWG : Set where
  field
    g : Gender
    n : Name g

{- ∃ x : A.B is true iff there exists an a:A such that B[x := a] is true.
   Therefore a proof of ∃ x : A. B ia a pair <a,p> where a:A and p is a 
   proof of B[x:=a]. THUS...
   we can identify ∃ x : A. B with (x:A)×B -}

record ∃r (A : Set)(B : A → Set) : Set where
  field
    a : A
    b : B a

f2 : ℕ
f2 = let h : ℕ → ℕ
         h m = sum m 3
     in  h (5)

f3 : ℕ → ℕ
f3 = let f4 : ℕ → ℕ → ℕ
         f4 x y = sum x y
     in f4 5

f5 : ℕ → ℕ
f5 n = let m : ℕ
           m = sum n 2
       in sum m m

{-Prove that ((A → A) → A)→ A 
  For De-activate Agda (C-c C-x C-d)-}

postulate A : Set
fp : ((A → A) → A) → A
fp a-a-a = let a-a : A → A
               a-a = \a → a
           in a-a-a a-a

postulate B : Set
gp : (A → B → A)
gp a = let b-a : B → A
           b-a = \x → a
       in b-a

lemma0 : Set
lemma0 = A → B → A
lm0 : lemma0
lm0 = \(a : A) → (\(x : B) → a)


hp : (A → B → B)
hp a = let b-b : B → B
           b-b = \x → x
       in b-b



lemma1 : Set
lemma1 = A → (A → B) → B

lm1 : lemma1
lm1 = \(a : A) → \(a-b : A → B) → a-b a



record general : Set where
  field
    a : A
    b : A


record prod (A B : Set) : Set where
  field
    first : A
    second : B

p23 : prod ℕ ℕ
p23 = record{ first = 2; second = 3}

p34 : prod ℕ ℕ
prod.first p34 = 3
prod.second p34 = 4

postulate C : Set
postulate D : Set

record AB : Set where
  field
    a : A
    b : B

record CD : Set where
  field
    c : C
    d : D

lemma2 : AB → (A → C) → (B → D) → CD
lemma2 ab a-c b-d = let a' : A
                        a' = AB.a ab
                        b' : B
                        b' = AB.b ab
                        c' : C
                        c' = a-c a'
                        d' : D
                        d' = b-d b'
                    in record{c = c' ; d = d'}


data ⊥ : Set where
  
fbot : ⊥ → Bool
fbot ()

data ⊤ : Set where
  tt : ⊤

q : ⊤ → Bool
q tt = true

{-another way to define ⊤ is by empty record-}

record ⊤' : Set where

{-then the element true of ⊤ is defined as follow-}

true' : ⊤'
true' = record{}

¬ : Set → Set
¬ A = A → ⊥

data Shape : Set where
  triangle : Shape
  rectangle : Shape
  circle : Shape
  ellips : Shape

IsSmooth : Shape → Set
IsSmooth triangle = ⊥
IsSmooth rectangle = ⊥
IsSmooth _ = ⊤

geo : (s : Shape) → IsSmooth s → Shape
geo circle _ = circle
geo ellips _ = ellips
geo triangle ()
geo rectangle ()

data Stack (A : Set) : Set where
  empty : Stack A
  push : A → Stack A → Stack A

NonEmpty : {A : Set} → Stack A → Set
NonEmpty empty = ⊥
NonEmpty (push _ _) = ⊤

top : {A : Set} → (s : Stack A) → NonEmpty s → A
top empty ()
top (push a _) _ = a

{-Convert Boolean value into a formula-}

Atom : Bool → Set
Atom true = ⊤
Atom false = ⊥

ands : Bool → Bool → Set
ands b1 b2 = Atom(b1 ∧ b2)

ors : Bool → Bool → Set
ors b1 b2 = Atom(b1 ∨ b2)

data TrafficLight : Set where
  green : TrafficLight
  yellow : TrafficLight
  red : TrafficLight

pass : TrafficLight → TrafficLight → Bool
pass green green = true
pass red red = true
pass yellow yellow = true
pass _ _ = false


{-Or we can convert this function into a formula by:-}

equal : TrafficLight → TrafficLight → Set
equal t1 t2 = Atom(pass t1 t2)

_<B_ : Bool → Bool → Bool
false <B b = b
true <B _ = false

_<S_ : Bool → Bool → Set
a <S b = Atom(a <B b)

Lemma3 : Set
Lemma3 = (a : Bool) → (a <S a) → ⊥
lemma3 : Lemma3
lemma3 true ()
lemma3 false ()

{-We just prove that ¬ (a <S a) -}


data ∃d (A : Set) (B : A → Set) : Set where
  exists : (a : A) → B a → ∃d A B

_=₂_ : Bool → Bool → Bool
true =₂ b = true
false =₂ b = not b

_=₃_ : Bool → Bool → Set
b =₃ b' = Atom(b =₂ b')

{-introducing formula ∃(b:Bool).a =₂ not b depending on a:Bool-}

record Lemma4 (a : Bool) : Set where
  field
    b : Bool
    ab : a =₃ not b   {-here we need an evidence that a=not b and ab is
                        that evidence. If we replace =₃ with =₂ it 
                        produce type error -}

{- The statement ∀(a:Bool).∃(b:Bool). a=₂ (not b) is as follow  -}

Lemma5 : Set
Lemma5 = (a : Bool) → Lemma4 a

{-a proof of Lemma5 is an element of Lemma5, i.e, lemma5:Lemma5-}

lemma5 : Lemma5
lemma5 true = record{b = false ; ab = tt }  
lemma5 false = record{b = true ; ab = tt }

{-Note that tt:⊤ and ⊥ is not habitated.
  we show that proof ab of a=₃not b is tt-}

postulate _≡A_ : A → A → Set
postulate _≡B_ : B → B → Set

{-
_=AB_ : A × B → A × B → Set
(x1 , y1) =AB (x2 , y2) =
-}

Sym : (A : Set) → (A → A → Set) → Set
Sym A _≡_ = (a1 a2 : A) → a1 ≡ a2 → a2 ≡ a1

SymA : Set
SymA = Sym A _≡A_

SymB : Set
SymB = Sym B _≡B_

Lemma6 : (A → CD) → A → D
Lemma6 = \(a-cd : A → CD) → \(a : A) → CD.d (a-cd a)

Lemma6' : (A → CD) → A → C
Lemma6' = \(a-cd : A → CD) → \(a : A) → CD.c (a-cd a)

{-We just prove that (A → C ∧ D) → A → D -}


{-Traffic light. A<->A', B<->B' and there is a × road. we need safety property-}

data Colour : Set where
  red : Colour
  green : Colour

record PhysState : Set where
  field
    sigA : Colour
    sigB : Colour

{-if sigA = green means A is moving in its direction.-}

{-The set of control state is a set of states. A controller of the system 
  can choose each of these states should be safe and all safe states will
  be captured.-}

{-A complete set of control states consists of:
 allRed : all signals are red
 onlyAGreen : sigA = green and sigB = red
 onlyBGreen : sigB = green and sigA = red.-}

data ControlState : Set where
  allRed : ControlState
  onlyAGreen : ControlState
  onlyBGreen : ControlState

{-we define the state of signals A and B depending on a control state.-}

toSigA : ControlState → Colour
toSigA allRed = red
toSigA onlyAGreen = green
toSigA onlyBGreen = red


toSigB : ControlState → Colour
toSigB allRed = red
toSigB onlyAGreen = red
toSigB onlyBGreen = green

{-now we can define physical state corresponding to a control state:-}

toPhysState : ControlState → PhysState
toPhysState c = record{sigA = toSigA c ; sigB = toSigB c}

{-we define when a physical state is safe:
  it is safe iff not both signals are green.-}


CorAux : Colour → Colour → Set
CorAux red _ = ⊤
CorAux green red = ⊤
CorAux green green = ⊥

Cor : PhysState → Set
Cor s = CorAux (PhysState.sigA s) (PhysState.sigB s)

{-now we show all control states are safe.-}

corProof : (s : ControlState) → Cor(toPhysState s)
corProof allRed = tt
corProof onlyAGreen = tt
corProof onlyBGreen = tt

{-in type theory A ∨ B ≡ A ⊕ B. We show A ⊕ B → B ⊕ A . -}

Lemma7 : A ⊕ B → B ⊕ A
Lemma7 (inl a) = inr a
Lemma7 (inr b) = inl b

pred : ℕ → ℕ
pred zero = zero
pred (succ n) = n

halt : ℕ → ℕ
halt zero = zero
halt (succ n) = f(pred n)

{-check-termination fails because of the undecidability of the halting problem.-}

fib : ℕ → ℕ
fib zero = 1
fib (succ zero) = 1
fib (succ (succ n)) = sum (fib n) (fib (succ n))

{-Equality on ℕ.-}

_≡Bool_ : ℕ → ℕ → Bool
zero ≡Bool zero = true
succ n ≡Bool succ m = n ≡Bool m
_ ≡Bool _ = false

_≡N_ : ℕ → ℕ → Set
n ≡N m = Atom(n ≡Bool m)

Lemma8 : Set
Lemma8 = (n : ℕ) → n ≡N n

lemma8 : Lemma8
lemma8 zero = tt
lemma8 (succ n) = lemma8 n

{-Symmetry in ℕ.-}

Lemma9 : Set
Lemma9 = (n m : ℕ) → n ≡N m → m ≡N n

lemma9 : Lemma9
lemma9 zero zero _ = tt
lemma9 (succ n) zero ()
lemma9 zero (succ m) ()
lemma9 (succ n) (succ m) nm = lemma9 n m nm


open import Relation.Binary.PropositionalEquality
open import Level

record Functor {a} (F : Set a → Set a) : Set (suc a) where
  field
    fmap : ∀ {A B} → (A → B) → F A → F B

instance
  NaturalFunctor : Functor list
  NaturalFunctor = record{fmap = map}

