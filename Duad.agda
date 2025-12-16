{-# OPTIONS --without-K --safe #-}

module Duad where

-- Various imports from Agda's standard library

open import Data.Integer using (ℤ; NonZero; _*_; +_; _+_; _-_; -_)
open import Data.Integer.Properties using (i*j≢0; *-assoc; *-comm; +-comm; *-distribʳ-+; *-distribˡ-+; +-assoc; neg-distribʳ-*)
open import Data.Product using (proj₁; proj₂; _,_)
open import Level using (0ℓ)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; module ≡-Reasoning)


module Definition where

  open Data.Product using (_×_)

  -- A duad is represented with a pair of integers

  -- Set is an Agda primitive essentially meaning the "type of types".
  -- Thus, the declaration "Duad : Set" should be read as "Duad is a type",
  -- and should not be thought of as indicating that Duad is a
  -- "set" in the classical sense.

  Duad : Set
  Duad = ℤ × ℤ

open Definition

-- Example duads

-- [3,5]
_ : Duad
_ = + 3 , + 5

-- [7,-9]
_ : Duad
_ = + 7 , - + 9

-- Basic operations on duads
module Operations where

  -- Addition
  _⊕_ : Duad → Duad → Duad
  (a , b) ⊕ (c , d) = a * d + b * c , b * d

  -- Multiplication
  _×_ : Duad → Duad → Duad
  (a , b) × (c , d) = a * c , b * d

  -- Subtraction
  _⊝_ : Duad → Duad → Duad
  (a , b) ⊝ (c , d) = a * d - b * c , b * d

  -- Division
  _÷_ : Duad → Duad → Duad
  (a , b) ÷ (c , d) = a * d , b * c

  infixl 7 _×_ _÷_
  infixl 6 _⊕_ _⊝_

  -- height
  h : Duad → ℤ
  h (a , b) = b

  -- length
  l : Duad → ℤ
  l (a , b) = a

  scale-by : ℤ → Duad → Duad
  scale-by r (a , b) = r * a , r * b

-- Basic laws of arithmetic
module BasicLaws where

  open Operations
  open ≡-Reasoning

  -- Helper function for proving equality of duads:
  -- (a , b) ≡ (c , d) whenever a ≡ c and b ≡ d.
  mk-≡ : ∀ {a b c d : ℤ} → a ≡ c → b ≡ d → (a , b) ≡ (c , d)
  mk-≡ = ≡.cong₂ _,_

  -- Addition is commutative
  ⊕-comm : ∀ p q → p ⊕ q ≡ q ⊕ p
  ⊕-comm (a , b) (c , d) = mk-≡ ad+bc≡cb+da bd≡db
    where
      ad+bc≡cb+da : a * d + b * c ≡ c * b + d * a
      ad+bc≡cb+da = begin
          a * d + b * c ≡⟨ ≡.cong₂ _+_ (*-comm a d) (*-comm b c) ⟩
          d * a + c * b ≡⟨ +-comm (d * a) (c * b) ⟩
          c * b + d * a ∎
      bd≡db : b * d ≡ d * b
      bd≡db = *-comm b d

  -- Multiplication is commutative
  ×-comm : ∀ p q → p × q ≡ q × p
  ×-comm (a , b) (c , d) = mk-≡ (*-comm a c) (*-comm b d)

  -- Addition is associative
  ⊕-assoc : ∀ p q r → (p ⊕ q) ⊕ r ≡ p ⊕ (q ⊕ r)
  ⊕-assoc (a , b) (c , d) (e , f) = mk-≡ ≡₁ (*-assoc b d f)
    where
      open ≡.≡-Reasoning
      ≡₁ : (a * d + b * c) * f + b * d * e ≡ a * (d * f) + b * (c * f + d * e)
      ≡₁ = begin
          (a * d + b * c) * f + b * d * e         ≡⟨ ≡.cong (_+ b * d * e) (*-distribʳ-+ f (a * d) (b * c)) ⟩
          (a * d * f + b * c * f) + b * d * e     ≡⟨ +-assoc (a * d * f) (b * c * f) (b * d * e) ⟩
          a * d * f + (b * c * f + b * d * e)     ≡⟨ ≡.cong₂ (λ x y → a * d * f + (x + y)) (*-assoc b c f) (*-assoc b d e) ⟩
          a * d * f + (b * (c * f) + b * (d * e)) ≡⟨ ≡.cong (λ x → a * d * f + x) (*-distribˡ-+ b (c * f) (d * e)) ⟨
          a * d * f + (b * (c * f + d * e))       ≡⟨ ≡.cong (_+ (b * (c * f + d * e))) (*-assoc a d f) ⟩
          a * (d * f) + b * (c * f + d * e)       ∎

  -- Multiplication is associative
  ×-assoc : (p q r : Duad) → (p × q) × r ≡ p × (q × r)
  ×-assoc (a , b) (c , d) (e , f) = mk-≡ (*-assoc a c e) (*-assoc b d f)

  -- Multiplication distributes over addition from the left, when scaled by height
  ×-distribˡ-⊕ : ∀ p q r → scale-by (h p) (p × (q ⊕ r)) ≡ (p × q) ⊕ (p × r)
  ×-distribˡ-⊕ (a , b) (c , d) (e , f) = mk-≡ ≡₁ ≡₂
    where
      ≡₁ : b * (a * (c * f + d * e)) ≡ (a * c) * (b * f) + (b * d) * (a * e)
      ≡₁ = begin
          b * (a * (c * f + d * e))               ≡⟨ ≡.cong (b *_) (*-distribˡ-+ a (c * f) (d * e)) ⟩
          b * (a * (c * f) + a * (d * e))         ≡⟨ ≡.cong₂ (λ x y → b * (x + y)) (*-assoc a c f) (*-assoc a d e) ⟨
          b * ((a * c) * f + (a * d) * e)         ≡⟨ *-distribˡ-+ b ((a * c) * f) ((a * d) * e) ⟩
          b * ((a * c) * f) + b * ((a * d) * e)   ≡⟨ ≡.cong₂ (λ x y → x + b * (y * e)) (*-assoc b (a * c) f) (*-comm d a) ⟨
          (b * (a * c)) * f + b * ((d * a) * e)   ≡⟨ ≡.cong₂ (λ x y → x * f + b * y) (*-comm b (a * c)) (*-assoc d a e) ⟩
          ((a * c) * b) * f + b * (d * (a * e))   ≡⟨ ≡.cong₂ _+_ (*-assoc (a * c) b f) (≡.sym (*-assoc b d (a * e))) ⟩
          (a * c) * (b * f) + (b * d) * (a * e)   ∎

      ≡₂ : b * (b * (d * f)) ≡ (b * d) * (b * f)
      ≡₂ = begin
          b * (b * (d * f)) ≡⟨ ≡.cong (b *_) (*-assoc b d f) ⟨
          b * ((b * d) * f) ≡⟨ ≡.cong (λ x → b * (x * f)) (*-comm b d) ⟩
          b * ((d * b) * f) ≡⟨ ≡.cong (b *_) (*-assoc d b f) ⟩
          b * (d * (b * f)) ≡⟨ *-assoc b d (b * f) ⟨
          (b * d) * (b * f) ∎

  -- Multiplication distributes over addition from the right, when scaled by height
  ×-distribʳ-⊕ : ∀ p q r → scale-by (h r) ((p ⊕ q) × r) ≡ (p × r) ⊕ (q × r)
  ×-distribʳ-⊕ p q r = begin
      scale-by (h r) ((p ⊕ q) × r)  ≡⟨ ≡.cong (scale-by (h r)) (×-comm (p ⊕ q) r) ⟩
      scale-by (h r) (r × (p ⊕ q))  ≡⟨ ×-distribˡ-⊕ r p q ⟩
      (r × p) ⊕ (r × q)             ≡⟨ ≡.cong₂ _⊕_ (×-comm r p) (×-comm r q) ⟩
      (p × r) ⊕ (q × r)             ∎

  -- Secondary laws

  ⊕-⊝ : (p q r : Duad) → (p ⊕ q) ⊝ r ≡ p ⊕ (q ⊝ r)
  ⊕-⊝ (a , b) (c , d) (e , f) = mk-≡ ≡top (*-assoc b d f)
    where
      ≡top : (a * d + b * c) * f - (b * d) * e ≡ a * (d * f) + b * (c * f - d * e)
      ≡top = begin
          (a * d + b * c) * f - (b * d) * e           ≡⟨ ≡.cong (_- (b * d) * e) (*-distribʳ-+ f (a * d) (b * c)) ⟩
          ((a * d) * f + (b * c) * f) - (b * d) * e   ≡⟨ +-assoc (a * d * f) (b * c * f) (- (b * d * e)) ⟩
          (a * d) * f + ((b * c) * f - (b * d) * e)   ≡⟨ ≡.cong₂ (λ x y → a * d * f + (x - y)) (*-assoc b c f) (*-assoc b d e) ⟩
          (a * d) * f + (b * (c * f) - b * (d * e))   ≡⟨ ≡.cong (λ x → a * d * f + (b * (c * f) + x)) (neg-distribʳ-* b (d * e)) ⟩
          (a * d) * f + (b * (c * f) + b * - (d * e)) ≡⟨ ≡.cong (λ x → a * d * f + x) (*-distribˡ-+ b (c * f) (- (d * e))) ⟨
          (a * d) * f + b * (c * f - d * e)           ≡⟨ ≡.cong (_+ b * (c * f - d * e)) (*-assoc a d f) ⟩
          a * (d * f) + b * (c * f - d * e)           ∎

  ×-÷ : (p q r : Duad) → (p × q) ÷ r ≡ p × (q ÷ r)
  ×-÷ (a , b) (c , d) (e , f) = mk-≡ (*-assoc a c f) (*-assoc b d e)

  ÷-÷ : (p q r : Duad) → (p ÷ q) ÷ r ≡ p ÷ (q × r)
  ÷-÷ (a , b) (c , d) (e , f) = mk-≡ (*-assoc a d f) (*-assoc b c e)

  ÷-× : (p q r : Duad) → (p ÷ q) × r ≡ p ÷ (q ÷ r)
  ÷-× (a , b) (c , d) (e , f) = mk-≡ (*-assoc a d e) (*-assoc b c f)

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
