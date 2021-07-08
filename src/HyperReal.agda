module HyperReal where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Empty
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Level renaming ( suc to succ ; zero to Zero ; _⊔_ to _L⊔_ )
open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Binary.Definitions
open import Relation.Binary.Structures
open import nat
open import logic
open import bijection

HyperNat : Set
HyperNat = ℕ → ℕ

open _∧_
open Bijection

n1 : ℕ → ℕ
n1 n = proj1 (fun→ nxn n)

n2 : ℕ → ℕ
n2 n = proj2 (fun→ nxn n)

_n*_ : (i j : HyperNat ) → HyperNat
i n* j = λ k → i k * j k

_n+_ : (i j : HyperNat ) → HyperNat
i n+ j = λ k → i k + j k

hzero : HyperNat
hzero _ = 0 

h : (n : ℕ) → HyperNat
h n _ = n 

record _n=_  (i j : HyperNat ) :  Set where 
   field 
      =-map : Bijection ℕ ℕ 
      =-m : ℕ
      is-n= : (k : ℕ ) → k > =-m → i k ≡ j (fun→ =-map  k)

open _n=_

record _n≤_  (i j : HyperNat ) :  Set where 
   field 
      ≤-map : Bijection ℕ ℕ
      ≤-m : ℕ
      is-n≤ : (k : ℕ ) → k > ≤-m → i k ≤ j (fun→ ≤-map  k)

open _n≤_

record _n<_  (i j : HyperNat ) :  Set where 
   field 
      <-map : Bijection ℕ ℕ
      <-m : ℕ
      is-n< : (k : ℕ ) → k > <-m → i k < j (fun→ <-map  k)

open _n<_

_n<=s≤_ :  (i j : HyperNat ) → (i n< j) ⇔ (( i n+ h 1 ) n≤ j )
_n<=s≤_ = {!!}

¬hn<0 : {x : HyperNat } → ¬ ( x n< h 0 )
¬hn<0 {x} x<0 = ⊥-elim ( nat-≤> (is-n< x<0 (suc (<-m x<0)) a<sa) 0<s )

postulate
   <-cmpn  : Trichotomous {Level.zero} _n=_  _n<_ 

n=IsEquivalence : IsEquivalence _n=_
n=IsEquivalence = record { refl = record {=-map = bid ℕ ; =-m = 0 ; is-n= = λ _ _ → refl}
  ; sym = λ xy →  record {=-map = bi-sym ℕ ℕ (=-map xy) ; =-m =  =-m xy ; is-n= = λ k lt → {!!} } -- (is-n= xy k lt) }
  ; trans =  λ xy yz →  record {=-map = bi-trans ℕ ℕ ℕ (=-map xy) (=-map yz) ; =-m =  {!!} ; is-n= = λ k lt → {!!} } }

HNTotalOrder : IsTotalPreorder _n=_ _n≤_ 
HNTotalOrder = record {
     isPreorder = record {
              isEquivalence = n=IsEquivalence
            ; reflexive     = λ eq → record { ≤-map = =-map eq ; ≤-m = =-m eq ; is-n≤ = {!!} }
            ; trans         = trans1 }
    ; total = total
  } where
      open import Data.Sum.Base using (_⊎_)
      open _⊎_
      total : (x y : HyperNat ) → (x n≤ y) ⊎ (y n≤ x)
      total x y with <-cmpn x y 
      ... | tri< a ¬b ¬c = inj₁ {!!}
      ... | tri≈ ¬a b ¬c = {!!}
      ... | tri> ¬a ¬b c = {!!}
      trans1 : {i j k : HyperNat} →  i n≤ j → j n≤ k → i n≤ k
      trans1 = {!!}

record n-finite (i : HyperNat ) : Set where
  field
     val : ℕ
     is-val : i n= h val

n-infinite :  (i : HyperNat ) → Set
n-infinite i = (j : ℕ ) → h j n≤ i

n-linear : HyperNat
n-linear i = i

n-linear-is-infnite : n-infinite n-linear
n-linear-is-infnite i = record { ≤-map = bid ℕ ; ≤-m = i ; is-n≤ = λ k lt → <to≤ lt }

¬-infinite-n-finite :  (i : HyperNat ) →  n-finite i → ¬ n-infinite i
¬-infinite-n-finite = {!!}

data HyperZ : Set where
   hz : HyperNat → HyperNat → HyperZ 

hZ : ℕ → ℕ → HyperZ
hZ x y = hz (λ _ → x) (λ _ → y )

_z+_ : (i j : HyperZ ) → HyperZ
hz i i₁ z+ hz j j₁ = hz ( i n+ j ) (i₁ n+ j₁ )

_z*_ : (i j : HyperZ ) → HyperZ
hz i i₁ z* hz j j₁ = hz (λ k → i k * j k + i₁ k * j₁ k ) (λ k →  i k * j₁ k - i₁ k * j k )

--  x0 - y0 ≡ x1 - y1
--  x0 + y1 ≡ x1 + y0
--
_z=_ :  (i j : HyperZ ) → Set
_z=_ (hz x0 y0) (hz x1 y1)  = (x0 n+ y1) n= (x1 n+ y0)

_z≤_ :  (i j : HyperZ ) → Set
_z≤_ (hz x0 y0) (hz x1 y1)  = (x0 n+ y1) n≤ (x1 n+ y0)

_z<_ :  (i j : HyperZ ) → Set
_z<_ (hz x0 y0) (hz x1 y1)  = (x0 n+ y1) n< (x1 n+ y0)

<-cmpz  : Trichotomous {Level.zero}  _z=_ _z<_
<-cmpz (hz x0 y0) (hz x1 y1)  = <-cmpn (x0 n+ y1) (x1 n+ y0) 

-z :  (i : HyperZ ) →  HyperZ 
-z (hz x y) = hz y x 

z-z=0 : (i : HyperZ ) → (i z+ (-z i)) z= hZ 0 0
z-z=0 = {!!}

z+infinite :  (i : HyperZ ) → Set
z+infinite i = (j : ℕ ) → hZ j 0 z≤ i

z-infinite :  (i : HyperZ ) → Set
z-infinite i = (j : ℕ ) → i z≤ hZ 0 j

import Axiom.Extensionality.Propositional
postulate f-extensionality : { n m : Level}  → Axiom.Extensionality.Propositional.Extensionality n m

---    x*y    ...... 0 0 0 0 ...
---    x      ...... 0 0 1 0 1 ....
---    y      ...... 0 1 0 1 0 ....

HNnzero* : {x y : HyperNat } → ¬ ( x n= h 0 ) → ¬ ( y n= h 0  ) → ¬ ( (x n* y) n= h 0 )
HNnzero* {x} {y} nzx nzy xy0 = hn1 where
   hn2 : ( h 0 n< x ) → ( h 0 n< y  ) →  ¬ ( (x n* y) n= h 0 )
   hn2 0<x 0<y  xy0 = ⊥-elim ( nat-≡< (sym (is-n= xy0 (suc mxy) {!!} )) {!!}  ) where
       mxy : ℕ
       mxy = <-m 0<x ⊔ <-m 0<y ⊔ =-m xy0
   hn1 : ⊥
   hn1 with <-cmpn x (h 0)
   ... | tri≈ ¬a b ¬c = nzx b
   ... | tri< a ¬b ¬c = ⊥-elim ( ¬hn<0 a)
   hn1 | tri> ¬a ¬b c with <-cmpn y (h 0)
   ... | tri< a ¬b₁ ¬c = ⊥-elim ( ¬hn<0 a)
   ... | tri≈ ¬a₁ b ¬c = nzy b
   ... | tri> ¬a₁ ¬b₁ c₁ = hn2 c c₁ xy0

HZzero : HyperZ → Set
HZzero z = hZ 0 0 z= z

HZzero? : ( i : HyperZ ) → Dec (HZzero i)
HZzero? = {!!}

data HyperR : Set where
   hr :  HyperZ → (k : HyperNat ) → ((i : ℕ) → 0 < k i) → HyperR

HZnzero* : {x y : HyperZ } → ¬ ( HZzero x ) → ¬ ( HZzero y ) → ¬ ( HZzero (x z* y) )
HZnzero* {x} {y} nzx nzy nzx*y = {!!}

HRzero : HyperR → Set
HRzero (hr i j nz ) = HZzero i

R0 : HyperR
R0 = hr (hZ 0 0) (h 1) {!!}

record Rational : Set where
  field
     rp rm k : ℕ
     0<k : 0 < k

hR :  ℕ → ℕ → (k : HyperNat ) → ((i : ℕ) → 0 < k i) → HyperR
hR x y k ne = hr (hZ x y) k ne

rH : (r : Rational ) → HyperR
rH r =  hr (hZ (Rational.rp r) (Rational.rm r)) (h (Rational.k r)) {!!}

--
--  z0 / y0 = z1 / y1 ← z0 * y1 = z1 * y0
--
_h=_ :  (i j : HyperR ) → Set
hr z0 k0 ne0 h= hr z1 k1 ne1  = (z0 z* (hz k1 (h 0))) z= (z1 z* (hz k0 (h 0)))

_h≤_ :  (i j : HyperR ) → Set
hr z0 k0 ne0 h≤ hr z1 k1 ne1  = (z0 z* (hz k1 (h 0))) z≤ (z1 z* (hz k0 (h 0)))

_h<_ :  (i j : HyperR ) → Set
hr z0 k0 ne0 h< hr z1 k1 ne1  = (z0 z* (hz k1 (h 0))) z< (z1 z* (hz k0 (h 0)))

<-cmph  : Trichotomous {Level.zero}  _h=_ _h<_
<-cmph (hr z0 k0 ne0 ) ( hr z1 k1 ne1 ) = <-cmpz  (z0 z* (hz k1 (h 0)))  (z1 z* (hz k0 (h 0)))

_h*_ : (i j : HyperR) → HyperR
hr x k nz h* hr y k₁ nz₁ = hr ( x z* y ) ( k n* k₁ ) {!!}

_h+_ : (i j : HyperR) → HyperR
hr x k nz h+ hr y k₁ nz₁ = hr ( (x z* (hz k hzero)) z+  (y z* (hz k₁ hzero)) ) (k n* k₁) {!!}

-h : (i : HyperR) → HyperR
-h (hr x k nz) = hr (-z x) k nz

inifinitesimal-R : (inf : HyperR) → Set
inifinitesimal-R inf = ( r : Rational ) → R0 h< rH r → ( -h (rH r) h< inf ) ∧ ( inf h< rH r)

1/x : HyperR
1/x = hr (hZ 1 0) n-linear {!!}

1/x-is-inifinitesimal : inifinitesimal-R 1/x
1/x-is-inifinitesimal r 0<r = ⟪ {!!} , {!!} ⟫

HyperReal :  Set 
HyperReal = ℕ  → HyperR

HR→HRl : HyperR → HyperReal
HR→HRl (hr (hz x y) k ne) k1 = hr (hz (λ k2 → (x k1)) (λ k2 → (x k1))) k ne

HRl→HR : HyperReal → HyperR
HRl→HR r = hr (hz (λ k → {!!}) (λ k → {!!}) ) factor {!!} where
   factor : HyperNat 
   factor n = {!!}
   fne : (n : ℕ) → ¬ (factor n= h 0)
   fne = {!!}

_≈_ : (x y : HyperR ) → Set
x ≈ y = inifinitesimal-R (x h+ ( -h y )) 

is-inifinitesimal : {x : HyperR } → inifinitesimal-R x → x ≈ R0
is-inifinitesimal {x} inf = {!!}

record Standard : Set where
   field
      standard          : HyperR → HyperR
      is-standard       : {x : HyperR } → x ≈ standard x
      standard-unique   : {x y : HyperR } →  x ≈ y → standard x ≡ standard y
      st-inifinitesimal : {x : HyperR } → inifinitesimal-R x → st x ≡ R0

postulate
   ST : Standard

open Standard

st :  HyperR → HyperR
st x = standard ST x



