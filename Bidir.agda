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
    i-if    : ∀ {G t e e₁ e₂} → G ⊢c e ⇒ TBool → G ⊢i e₁ ⇒ t → G ⊢i e₂ ⇒ t → G ⊢i (if e e₁ e₂) ⇒ t
    i-ann   : ∀ {G e t} → G ⊢c e ⇒ t → G ⊢i (e ∶ t) ⇒ t
  
  data _⊢c_⇒_ : Gam → Term → Ty → Set where
    c-lam : ∀ {G t t' e} → (G ,, t) ⊢c e ⇒ t' → G ⊢c (lam e) ⇒ (t ⇒ t')
    c-if  : ∀ {G t e₁ e₂ e₃} → G ⊢c e₁ ⇒ TBool → G ⊢c e₂ ⇒ t → G ⊢c e₃ ⇒ t → G ⊢c (if e₁ e₂ e₃) ⇒ t
    c-app : ∀ {G t t' e₁ e₂} → G ⊢i e₁ ⇒ (t ⇒ t') → G ⊢c e₂ ⇒ t → G ⊢c (app e₁ e₂) ⇒ t'
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
  infer G (app e e₁) | ok .e TBool d = bad (app e e₁)
  infer G (app e e₁) | ok .e (t ⇒ t₁) d with check G e₁ t
  infer G (app e e₁) | ok .e (t ⇒ t₁) d₁ | ok .e₁ .t d = ok (app e e₁) t₁ (i-app d₁ d)
  infer G (app e e₁) | ok .e (t ⇒ t₁) d | bad .e₁ .t = bad (app e e₁)
  infer G (app e e₁) | bad .e = bad (app e e₁)
  infer G (if e e₁ e₂) with check G e TBool | infer G e₁ | infer G e₂ 
  infer G (if e e₁ e₂) | ok .e .TBool d | ok .e₁ t d₁ | ok .e₂ t₁ d₂ with t ≡-ty t₁ 
  infer G (if e e₁ e₂) | ok .e .TBool d | ok .e₁ .t₁ d₁ | ok .e₂ t₁ d₂ | yes refl = ok (if e e₁ e₂) t₁ (i-if d d₁ d₂)
  infer G (if e e₁ e₂) | ok .e .TBool d | ok .e₁ t d₁ | ok .e₂ t₁ d₂ | no ¬p = bad (if e e₁ e₂)
  infer G (if e e₁ e₂) | ok .e .TBool d | ok .e₁ t d₁ | bad .e₂ = bad (if e e₁ e₂)
  infer G (if e e₁ e₂) | ok .e .TBool d | bad .e₁ | r = bad (if e e₁ e₂)
  infer G (if e e₁ e₂) | bad .e .TBool | q | r = bad (if e e₁ e₂)
  infer G (e ∶ t) with check G e t
  infer G (e ∶ t) | ok .e .t d = ok (e ∶ t) t (i-ann d)
  infer G (e ∶ t) | bad .e .t = bad (e ∶ t)

  check : ∀ (G : Gam)(e : Term)(t : Ty) → Check G e t
  check G (const b) t with t ≡-ty TBool
  check G (const b) .TBool | yes refl = ok (const b) TBool (c-ann i-const)
  check G (const b) t | no ¬p = bad (const b) t
  check G (var v) t with infer G (var v) 
  check G (var v) t₁ | ok .(var v) t d with t₁ ≡-ty t 
  check G (var v) .t | ok .(var v) t d | yes refl = ok (var v) t (c-ann d)
  check G (var v) t₁ | ok .(var v) t d | no ¬p = bad (var v) t₁
  check G (var v) t | bad .(var v) = bad (var v) t
  check G (lam e) TBool = bad (lam e) TBool
  check G (lam e) (t ⇒ t₁) with check (G ,, t) e t₁
  check G (lam e) (t ⇒ t₁) | ok .e .t₁ d = ok (lam e) (t ⇒ t₁) (c-lam d)
  check G (lam e) (t ⇒ t₁) | bad .e .t₁ = bad (lam e) (t ⇒ t₁)
  check G (app e e₁) t with infer G e 
  check G (app e e₁) t₁ | ok .e TBool d = bad (app e e₁) t₁
  check G (app e e₁) t₂ | ok .e (t ⇒ t₁) d with t₁ ≡-ty t₂ | check G e₁ t 
  check G (app e e₁) t₂ | ok .e (t ⇒ .t₂) d₁ | yes refl | ok .e₁ .t d = ok (app e e₁) t₂ (c-app d₁ d)
  check G (app e e₁) t₂ | ok .e (t ⇒ t₁) d | yes p | bad .e₁ .t = bad (app e e₁) t₂
  check G (app e e₁) t₂ | ok .e (t ⇒ t₁) d | no ¬p | q = bad (app e e₁) t₂
  check G (app e e₁) t | bad .e = bad (app e e₁) t
  check G (if e e₁ e₂) t with check G e TBool | check G e₁ t | check G e₂ t 
  check G (if e e₁ e₂) t | ok .e .TBool d | ok .e₁ .t d₁ | ok .e₂ .t d₂ = ok (if e e₁ e₂) t (c-if d d₁ d₂)
  check G (if e e₁ e₂) t | ok .e .TBool d | ok .e₁ .t d₁ | bad .e₂ .t = bad (if e e₁ e₂) t
  check G (if e e₁ e₂) t | ok .e .TBool d | bad .e₁ .t | z = bad (if e e₁ e₂) t
  check G (if e e₁ e₂) t | bad .e .TBool | y | z = bad (if e e₁ e₂) t
  check G (e ∶ t') t with infer G e
  check G (e ∶ t') t₁ | ok .e t d with t ≡-ty t' | t' ≡-ty t₁ 
  check G (e ∶ .t₁) t₁ | ok .e .t₁ d | yes refl | yes refl = ok (e ∶ t₁) t₁ (c-ann (i-ann (c-ann d)))
  check G (e ∶ t') t₁ | ok .e t d | yes p | no ¬p = bad (e ∶ t') t₁
  check G (e ∶ t') t₁ | ok .e t d | no ¬p | p' = bad (e ∶ t') t₁
  check G (e ∶ t') t | bad .e = bad (e ∶ t') t
  
