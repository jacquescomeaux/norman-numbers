{-# OPTIONS --without-K --safe #-}

module Duad where

-- Various imports from Agda's standard library

open import Data.Integer using (ℤ; NonZero; _*_; +_; _+_; _-_; -_)
open import Data.Integer.Properties using (i*j≢0; *-assoc; *-comm; +-comm; *-distribʳ-+; *-distribˡ-+; +-assoc; neg-distribʳ-*)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Level using (0ℓ)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; module ≡-Reasoning)

-- A duad is represented with a pair of integers

-- Set is an Agda primitive essentially meaning the "type of types".
-- Thus, the declaration "Duad : Set" should be read as "Duad is a type",
-- and should not be thought of as indicating that Duad is a
-- "set" in the classical sense.

Duad : Set
Duad = ℤ × ℤ

-- Example duads

-- [3,5]
_ : Duad
_ = + 3 , + 5

-- [7,-9]
_ : Duad
_ = + 7 , - (+ 9)

-- Equivalence of (projective) duads is represented with a record type

record _~_ (p q : Duad) : Set where

  constructor mk~

  -- For duads p = (a , b) and q = (c , d),
  -- p ~ q when we can exhibit

  field

    -- a non-zero integer m
    m : ℤ
    .{{m-nz}} : NonZero m

    -- and a non-zero integer n
    n : ℤ
    .{{n-nz}} : NonZero n

    -- such that ma = nc
    ma≡nc : m * proj₁ p ≡ n * proj₁ q

    -- and mb = nd.
    mb≡nd : m * proj₂ p ≡ n * proj₂ q

infix 4 _~_

-- Properties of the relation _~_

-- Reflexive: For any duad p, p ~ p.

-- Choosing m = n = 1,
-- our proof obligations reduce (i.e. compute) down to
-- 1 * a ≡ 1 * a, and
-- 1 * b ≡ 1 * b,
-- both of which can be proven
-- by appealing to reflexivity
-- of Agda's built-in propositional equality (≡.refl).

~-refl : ∀ {p : Duad} → p ~ p
~-refl = mk~ (+ 1) (+ 1) ≡.refl ≡.refl

-- In fact, any (non-zero) value will do:
-- here we give a different proof by choosing m = n = 100.

_ : ∀ {p : Duad} → p ~ p
_ = mk~ (+ 100) (+ 100) ≡.refl ≡.refl

-- Symmetric: For any duads p q, p ~ q implies q ~ p.

-- On the left hand side, we use pattern matching
-- to deconstruct the proof that p ~ q
-- and give names to its components.
-- On the right hand side, we build up a proof
-- that q ~ p by swapping m and n
-- and appealing to symmetry of the underlying equality (≡.sym)
-- for the two equations.

~-sym : ∀ {p q : Duad} → p ~ q → q ~ p
~-sym (mk~ m n ma≡nc mb≡nd) = mk~ n m (≡.sym ma≡nc) (≡.sym mb≡nd)

-- Transitive: For any duads p q r, p ~ q and q ~ r implies q ~ p.

-- We use pattern-matching again to deconstruct
-- the given proofs that p ~ q and q ~ r,
-- but this time proving the two equations
-- requires more work.

~-trans : ∀ {p q r : Duad} → p ~ q → q ~ r → p ~ r
~-trans {p} {q} {r} (mk~ m₁ n₁ ma≡nc₁ mb≡nd₁) (mk~ m₂ n₂ ma≡nc₂ mb≡nd₂) = mk~ (m₁ * m₂) (n₁ * n₂) ≡₁ ≡₂
  where
    -- if both x and y are non-zero, then so is x * y
    instance
      _ : NonZero (m₁ * m₂)
      _ = i*j≢0 m₁ m₂
      _ : NonZero (n₁ * n₂)
      _ = i*j≢0 n₁ n₂
    -- Below we need commutativity and associativity of _*_,
    -- transitivity of _≡_, and congruence of _≡_ (if x ≡ y then f(x) ≡ f(y)).
    -- We make use of Agda's reasoning syntax to give step-by-step proofs.
    open ≡-Reasoning
    ≡₁ : m₁ * m₂ * proj₁ p ≡ n₁ * n₂ * proj₁ r
    ≡₁ = begin
        (m₁ * m₂) * proj₁ p     ≡⟨ ≡.cong (_* proj₁ p) (*-comm m₁ m₂) ⟩
        (m₂ * m₁) * proj₁ p     ≡⟨ *-assoc m₂ m₁ (proj₁ p) ⟩
        m₂ * (m₁ * proj₁ p)     ≡⟨ ≡.cong (m₂ *_) ma≡nc₁ ⟩
        m₂ * (n₁ * proj₁ q)     ≡⟨ *-assoc m₂ n₁ (proj₁ q) ⟨
        (m₂ * n₁) * proj₁ q     ≡⟨ ≡.cong (_* proj₁ q) (*-comm m₂ n₁) ⟩
        (n₁ * m₂) * proj₁ q     ≡⟨ *-assoc n₁ m₂ (proj₁ q) ⟩
        n₁ * (m₂ * proj₁ q)     ≡⟨ ≡.cong (n₁ *_) ma≡nc₂ ⟩
        n₁ * (n₂ * proj₁ r)     ≡⟨ *-assoc n₁ n₂ (proj₁ r) ⟨
        (n₁ * n₂) * proj₁ r     ∎
    ≡₂ : m₁ * m₂ * proj₂ p ≡ n₁ * n₂ * proj₂ r
    ≡₂ = begin
        (m₁ * m₂) * proj₂ p     ≡⟨ ≡.cong (_* proj₂ p) (*-comm m₁ m₂) ⟩
        (m₂ * m₁) * proj₂ p     ≡⟨ *-assoc m₂ m₁ (proj₂ p) ⟩
        m₂ * (m₁ * proj₂ p)     ≡⟨ ≡.cong (m₂ *_) mb≡nd₁ ⟩
        m₂ * (n₁ * proj₂ q)     ≡⟨ *-assoc m₂ n₁ (proj₂ q) ⟨
        (m₂ * n₁) * proj₂ q     ≡⟨ ≡.cong (_* proj₂ q) (*-comm m₂ n₁) ⟩
        (n₁ * m₂) * proj₂ q     ≡⟨ *-assoc n₁ m₂ (proj₂ q) ⟩
        n₁ * (m₂ * proj₂ q)     ≡⟨ ≡.cong (n₁ *_) mb≡nd₂ ⟩
        n₁ * (n₂ * proj₂ r)     ≡⟨ *-assoc n₁ n₂ (proj₂ r) ⟨
        (n₁ * n₂) * proj₂ r     ∎

-- The reflexivity, symmetry, and transitivity proofs
-- above are packaged into single record witnessing
-- that _~_ is a equivalence relation.

~-isEquiv : IsEquivalence _~_
~-isEquiv = record
    { refl = ~-refl
    ; sym = ~-sym
    ; trans = ~-trans
    }

-- Duads form a setoid (a type equipped with an equivalence relation),
-- the p-duads (projective duads).

p-Duad : Setoid 0ℓ 0ℓ
p-Duad = record
    { Carrier = Duad
    ; _≈_ = _~_
    ; isEquivalence = ~-isEquiv
    }
