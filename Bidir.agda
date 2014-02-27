module Bidir where

open import Data.Bool
open import Data.List
open import Data.List.Any hiding (index)
open Data.List.Any.Membership-≡
open import Data.Product
open import Data.Nat

open import Relation.Nullary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality

-- Bidirectional type checker for STLC with booleans

data Ty : Set where
  TBool : Ty
  _⇒_   : Ty → Ty → Ty

inv-⇒ : ∀ {t t' t₁ t₁' : Ty} → t ⇒ t' ≡ t₁ ⇒ t₁' → t ≡ t₁ × t' ≡ t₁'
inv-⇒ refl = refl , refl

_≡-ty_ : Decidable {A = Ty} _≡_
TBool ≡-ty TBool = yes refl
TBool ≡-ty (t' ⇒ t'') = no (λ ())
(t ⇒ t₁) ≡-ty TBool = no (λ ())
(t ⇒ t₁) ≡-ty (t' ⇒ t'') with t ≡-ty t' | t₁ ≡-ty t'' 
(.t' ⇒ .t'') ≡-ty (t' ⇒ t'') | yes refl | yes refl = yes refl
(t ⇒ t₁) ≡-ty (t' ⇒ t'') | yes p | no ¬p = no (λ ctr → ¬p (proj₂ (inv-⇒ ctr)))
(t ⇒ t₁) ≡-ty (t' ⇒ t'') | no ¬p | y = no (λ ctr → ¬p (proj₁ (inv-⇒ ctr)))

Gam : Set
Gam = List Ty

_,,_ : Gam -> Ty -> Gam
G ,, t = t ∷ G

data Term : Set where
  const : Bool → Term
  var   : ℕ → Term
  lam   : Term → Term
  app   : Term → Term → Term
  if    : Term → Term → Term → Term
  _∶_   : Term → Ty → Term

index : ∀ {A : Set}{x : A}{xs} → x ∈ xs → ℕ
index (here px) = zero
index (there p) = suc (index p)

data Lookup {A : Set}(xs : List A) : ℕ → Set where
  inside  : (x : A)(p : x ∈ xs) → Lookup xs (index p)
  outside : (m : ℕ) → Lookup xs (length xs + m)

_!_ : {A : Set}(xs : List A)(n : ℕ) → Lookup xs n
[] ! n = outside n
(x ∷ xs) ! zero  = inside x (here refl)
(x ∷ xs) ! suc n with xs ! n 
(x₁ ∷ xs) ! suc .(index p) | inside x p = inside x (there p)
(x ∷ xs) ! suc .(length xs + m) | outside m = outside m


mutual
  data _⊢i_⇒_ : Gam → Term → Ty → Set where
    i-const : ∀ {G b} → G ⊢i (const b) ⇒ TBool
    i-var   : ∀ {G n t} → t ∈ G → G ⊢i (var n) ⇒ t
    i-app   : ∀ {G t t' e₁ e₂} → G ⊢i e₁ ⇒ (t ⇒ t') → G ⊢c e₂ ⇒ t → G ⊢i (app e₁ e₂) ⇒ t'
    i-ann   : ∀ {G e t} → G ⊢c e ⇒ t → G ⊢i (e ∶ t) ⇒ t
  
  data _⊢c_⇒_ : Gam → Term → Ty → Set where
    c-lam : ∀ {G t t' e} → (G ,, t) ⊢c e ⇒ t' → G ⊢c (lam e) ⇒ (t ⇒ t')
    c-ann : ∀ {G e t} → G ⊢i e ⇒ t → G ⊢c e ⇒ t

erase-i : ∀ {G e t} → G ⊢i e ⇒ t → Term
erase-i {G} {e} {t} _ = e

erase-c : ∀ {G e t} → G ⊢c e ⇒ t → Term
erase-c {G} {e} {t} _ = e

mutual
  data Infer (G : Gam) : Term → Set where
    ok  : (e : Term)(t : Ty)(d : G ⊢i e ⇒ t) → Infer G (erase-i d)
    bad : (e : Term) → Infer G e

  data Check (G : Gam) : Term → Ty → Set where
    ok  : (e : Term)(t : Ty)(d : G ⊢c e ⇒ t) → Check G (erase-c d) t
    bad : (e : Term)(t : Ty) → Check G e t

mutual 
  infer : ∀ (G : Gam)(e : Term) → Infer G e
  infer G (const b) = ok (const b) TBool i-const
  infer G (var v) with G ! v 
  infer G (var .(index p)) | inside x p = ok (var (index p)) x (i-var p)
  infer G (var .(length G + m)) | outside m = bad (var (length G + m))
  infer G (lam e) = bad (lam e)
  infer G (app e e₁) with infer G e 
  infer G (app e e₁) | ok .e t d = {!!}
  infer G (app e e₁) | bad .e = bad (app e e₁)
  infer G (if e e₁ e₂) = {!!}
  infer G (e ∶ x) = {!!}

  check : ∀ (G : Gam)(e : Term)(t : Ty) → Check G e t
  check G e t = {!!}
  
