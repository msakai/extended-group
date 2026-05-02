{-
体 F が x + y = 1 かつ x y = 1 を満たすような元を持たない時、F ∪ {∞} は

∞ ⊛ y = y
x ⊛ ∞ = x
x ⊛ y = (x y - 1) / (x + y - 1)  if x + y ≠ 1
x ⊛ y = ∞                        otherwise

で定義される演算によって群となる。

Checked with Agda version 2.8.0 and agda-stdlib-2.3

参考:
* https://x.com/MurakamiMath/status/1837434653634187342
-}

open import Algebra.Apartness.Bundles using (HeytingField)
open import Algebra.Core using (Op₁; Op₂)
open import Data.Product using (_×_)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (¬_)

module ExtendedGroup
  {c ℓ₁ ℓ₂}
  (HF : HeytingField c ℓ₁ ℓ₂)
  (#-dec : Decidable (HeytingField._#_ HF))
  where

open import Algebra.Apartness.Structures using (IsHeytingField)
open import Algebra.Apartness.Bundles using (HeytingCommutativeRing)
open import Algebra.Definitions
open import Algebra.Solver.Ring.AlmostCommutativeRing using (AlmostCommutativeRing; fromCommutativeRing)
open import Algebra.Structures
open import Algebra.Bundles
open import Data.Empty
open import Data.List
open import Data.Product
open import Data.Sum
open import Function using (_$_)
open import Level using (_⊔_; suc)
open import Relation.Binary
open import Relation.Nullary
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
import Algebra.Solver.Ring.NaturalCoefficients.Default

module Utils where
  open HeytingField HF hiding (refl; sym; trans)
  open IsEquivalence isEquivalence
  open import Algebra.Properties.Ring (CommutativeRing.ring (HeytingCommutativeRing.commutativeRing heytingCommutativeRing)) using (-1*x≈-x) public
  open import Algebra.Apartness.Properties.HeytingCommutativeRing heytingCommutativeRing using (#-congʳ)
  module Solver = Algebra.Solver.Ring.NaturalCoefficients.Default
    (CommutativeRing.commutativeSemiring (HeytingCommutativeRing.commutativeRing heytingCommutativeRing))
  open ≈-Reasoning setoid

  unique-inverse
    : ∀ {x₁ x₂} → (x₁≈x₂ : x₁ ≈ x₂)
    → ((x₁⁻¹ , _ , _) : Invertible _≈_ 1# _*_ x₁)
    → ((x₂⁻¹ , _ , _) : Invertible _≈_ 1# _*_ x₂)
    → x₁⁻¹ ≈ x₂⁻¹
  unique-inverse {x₁} {x₂} x₁≈x₂ (x₁⁻¹ , x₁⁻¹x₁≈1 , x₁x₁⁻¹≈1) (x₂⁻¹ , x₂⁻¹x₂≈1 , x₂x₂⁻¹≈1) = begin
    x₁⁻¹                ≈⟨ sym (*-identityʳ x₁⁻¹) ⟩
    x₁⁻¹ * 1#           ≈⟨ *-cong refl (sym x₂x₂⁻¹≈1) ⟩
    x₁⁻¹ * (x₂ * x₂⁻¹)  ≈⟨ sym (*-assoc x₁⁻¹ x₂ x₂⁻¹) ⟩
    (x₁⁻¹ * x₂) * x₂⁻¹  ≈⟨ *-cong (*-cong refl (sym x₁≈x₂)) refl ⟩
    (x₁⁻¹ * x₁) * x₂⁻¹  ≈⟨ *-cong x₁⁻¹x₁≈1 refl ⟩
    1# * x₂⁻¹           ≈⟨ *-identityˡ x₂⁻¹ ⟩
    x₂⁻¹
    ∎

  invert-right :  ∀ {x y z} → x * y ≈ z → ((y⁻¹ , _ , _)  : Invertible _≈_ 1# _*_ y) → x ≈ z * y⁻¹
  invert-right {x} {y} {z} x*y≈z (y⁻¹ , _ , y*y⁻¹≈1) = begin
    x              ≈⟨ sym (*-identityʳ x) ⟩
    x * 1#         ≈⟨ *-cong refl (sym y*y⁻¹≈1) ⟩
    x * (y * y⁻¹)  ≈⟨ sym (*-assoc x y y⁻¹) ⟩
    (x * y) * y⁻¹  ≈⟨ *-cong x*y≈z  refl ⟩
    z * y⁻¹
    ∎

  invert-left : ∀ {x y z} → x * y ≈ z → ((x⁻¹ , _ , _) : Invertible _≈_ 1# _*_ x) → y ≈ z * x⁻¹
  invert-left {x} {y} {z} x*y≈z = invert-right y*x≈z
    where
      y*x≈z : y * x ≈ z
      y*x≈z = trans (*-comm y x) x*y≈z

  invert-both
    : ∀ {x₁ y₁ x₂ y₂} → x₁ * y₁ ≈ x₂ * y₂
    → ((y₁⁻¹ , _ , _) : Invertible _≈_ 1# _*_ y₁)
    → ((y₂⁻¹ , _ , _) : Invertible _≈_ 1# _*_ y₂)
    → x₁ * y₂⁻¹ ≈ x₂ * y₁⁻¹
  invert-both {x₁} {y₁} {x₂} {y₂} x₁*y₁≈x₂*y₂ inv-y₁@(y₁⁻¹ , _ , _) inv-y₂@(y₂⁻¹ , _ , _) = sym x₂*y₁⁻¹≈x₁*y₂⁻¹
    where
      x₁≈x₂*y₂*y₁⁻¹ : x₁ ≈ (x₂ * y₂) * y₁⁻¹
      x₁≈x₂*y₂*y₁⁻¹ = invert-right x₁*y₁≈x₂*y₂ inv-y₁

      x₁≈x₂*y₁⁻¹*y₂ : x₁ ≈ (x₂ * y₁⁻¹) * y₂
      x₁≈x₂*y₁⁻¹*y₂ = begin
        x₁                ≈⟨ x₁≈x₂*y₂*y₁⁻¹ ⟩
        (x₂ * y₂) * y₁⁻¹  ≈⟨ *-assoc x₂ y₂ y₁⁻¹ ⟩
        x₂ * (y₂ * y₁⁻¹)  ≈⟨ *-cong refl (*-comm y₂ y₁⁻¹) ⟩
        x₂ * (y₁⁻¹ * y₂)  ≈⟨ sym (*-assoc x₂ y₁⁻¹ y₂) ⟩
        (x₂ * y₁⁻¹) * y₂
        ∎

      x₂*y₁⁻¹≈x₁*y₂⁻¹ : x₂ * y₁⁻¹ ≈ x₁ * y₂⁻¹
      x₂*y₁⁻¹≈x₁*y₂⁻¹ = invert-right (sym x₁≈x₂*y₁⁻¹*y₂) inv-y₂

  *-cancelʳ : ∀ a {x₁ x₂} → (Invertible _≈_ 1# _*_ a) → (x₁ * a ≈ x₂ * a) → x₁ ≈ x₂
  *-cancelʳ a {x₁} {x₂} (a⁻¹ , _ , a*a⁻¹≈1) x₁*a≈x₂*a = begin
    x₁              ≈⟨ sym (*-identityʳ x₁) ⟩
    x₁ * 1#         ≈⟨ *-cong refl (sym a*a⁻¹≈1) ⟩
    x₁ * (a * a⁻¹)  ≈⟨ sym (*-assoc x₁ a a⁻¹) ⟩
    (x₁ * a) * a⁻¹  ≈⟨ *-cong x₁*a≈x₂*a refl ⟩
    (x₂ * a) * a⁻¹  ≈⟨ *-assoc x₂ a a⁻¹ ⟩
    x₂ * (a * a⁻¹)  ≈⟨ *-cong refl a*a⁻¹≈1 ⟩
    x₂ * 1#         ≈⟨ *-identityʳ x₂ ⟩
    x₂
    ∎

  -‿-1≈1 : - (- 1#) ≈ 1#
  -‿-1≈1 = begin
    - (- 1#)                ≈⟨ sym (+-identityˡ _) ⟩
    0# - (- 1#)             ≈⟨ +-cong (sym (-‿inverseʳ 1#)) refl ⟩
    (1# + (- 1#)) - (- 1#)  ≈⟨ +-assoc _ _ _ ⟩
    1# + ((- 1#) - (- 1#))  ≈⟨ +-cong refl (-‿inverseʳ (- 1#)) ⟩
    1# + 0#                 ≈⟨ +-identityʳ _ ⟩
    1#
    ∎

  -1*-1≈1 : (- 1#) * (- 1#) ≈ 1#
  -1*-1≈1 = begin
    (- 1#) * (- 1#)  ≈⟨ -1*x≈-x (- 1#) ⟩
    - (- 1#)         ≈⟨ -‿-1≈1 ⟩
    1#
    ∎

  -0≈0 : - 0# ≈ 0#
  -0≈0 = begin
    - 0#     ≈⟨ sym (+-identityˡ (- 0#)) ⟩
    0# - 0#  ≈⟨ -‿inverseʳ _ ⟩
    0#
    ∎

  x≈y⇒x-y≈0 : ∀ {x y} → x ≈ y → x - y ≈ 0#
  x≈y⇒x-y≈0 {x} {y} x≈y = begin
    x - y      ≈⟨ +-cong x≈y refl ⟩
    y + (- y)  ≈⟨ -‿inverseʳ y ⟩
    0#
    ∎

  x-y≈0⇒x≈y : ∀ {x y} → x - y ≈ 0# → x ≈ y
  x-y≈0⇒x≈y {x} {y} x-y≈0 = begin
    x              ≈⟨ sym (+-identityʳ x) ⟩
    x + 0#         ≈⟨ +-cong refl (sym (-‿inverseˡ y)) ⟩
    x + (- y + y)  ≈⟨ sym (+-assoc x (- y) y) ⟩
    (x - y) + y    ≈⟨ +-cong x-y≈0 refl ⟩
    0# + y         ≈⟨ +-identityˡ y ⟩
    y
    ∎

  x+y≈1∧xy≈1⇒x²-x+1≈0 : ∀ {x y} → (x + y ≈ 1#) × (x * y ≈ 1#) → (x * x - x + 1# ≈ 0#)
  x+y≈1∧xy≈1⇒x²-x+1≈0 {x} {y} (x+y≈1 , x*y≈1) = begin
    x * x - x + 1#                               ≈⟨ +-cong (+-cong (sym (*-identityˡ (x * x))) (sym (-1*x≈-x x))) refl ⟩
    1# * (x * x) + (- 1#) * x + 1#               ≈⟨ +-cong (+-cong (*-cong (sym -1*-1≈1) refl) refl) refl ⟩
    (- 1#) * (- 1#) * (x * x) + (- 1#) * x + 1#  ≈⟨  solve 2 (λ x m → m :* m :* (x :* x) :+ m :* x :+ con 1 := m :* ((con 1 :+ m :* x) :* x) :+ con 1) refl x (- 1#) ⟩
    (- 1#) * ((1# + (- 1#) * x) * x) + 1#        ≈⟨ +-cong (*-cong refl (*-cong (+-cong refl (-1*x≈-x x)) refl)) refl ⟩
    (- 1#) * ((1# - x) * x) + 1#                 ≈⟨ +-cong (-1*x≈-x _) refl ⟩
    - ((1# - x) * x) + 1#                        ≈⟨ +-cong (-‿cong (*-cong (sym y≈1-x) refl)) refl ⟩
    - (y * x) + 1#                               ≈⟨ +-cong (-‿cong (*-comm y x)) refl ⟩
    - (x * y) + 1#                               ≈⟨ +-cong (-‿cong x*y≈1) refl ⟩
    - 1# + 1#                                    ≈⟨ -‿inverseˡ 1# ⟩
    0#
    ∎
    where
      open Solver

      y≈1-x : y ≈ 1# - x
      y≈1-x = begin
        y            ≈⟨ sym (+-identityʳ _) ⟩
        y + 0#       ≈⟨ +-cong refl (sym (-‿inverseʳ x)) ⟩
        y + (x - x)  ≈⟨ sym (+-assoc _ _ _) ⟩
        (y + x) - x  ≈⟨ +-cong (+-comm y x) refl ⟩
        (x + y) - x  ≈⟨ +-cong x+y≈1 refl ⟩
        1# - x
        ∎

  x²-x+1≈0⇒x+y≈1∧xy≈1 : ∀ {x} → (x * x - x + 1# ≈ 0#) → ∃[ y ] ((x + y ≈ 1#) × (x * y ≈ 1#))
  x²-x+1≈0⇒x+y≈1∧xy≈1 {x} x²-x+1≈0 = (y , (x+y≈1 , x*y≈1))
    where
      open Solver

      y = 1# - x

      x+y≈1 : x + y ≈ 1#
      x+y≈1 = begin
        x + y           ≈⟨ refl ⟩
        x + (1# - x)    ≈⟨ +-cong refl (+-comm _ _) ⟩
        x + (- x + 1#)  ≈⟨ sym (+-assoc _ _ _) ⟩
        (x - x) + 1#    ≈⟨ +-cong (-‿inverseʳ _) refl ⟩
        0# + 1#         ≈⟨ +-identityˡ 1# ⟩
        1#
        ∎

      x*y-1≈0 : x * y - 1# ≈ 0#
      x*y-1≈0 = begin
        x * y - 1#                               ≈⟨ refl ⟩
        x * (1# - x) - 1#                        ≈⟨ +-cong (*-cong refl (+-cong (sym -1*-1≈1) (sym (-1*x≈-x x)))) refl  ⟩
        x * ((- 1#) * (- 1#) + (- 1#) * x) - 1#  ≈⟨ solve 2 (\x m → x :* (m :* m :+ m :* x) :+ m := m :* (x :* x :+ m :* x :+ con 1)) refl x (- 1#) ⟩
        (- 1#) * (x * x + (- 1#) * x + 1#)       ≈⟨ *-cong refl (+-cong (+-cong (refl {x * x}) (-1*x≈-x x)) refl) ⟩
        (- 1#) * (x * x - x + 1#)                ≈⟨ -1*x≈-x _ ⟩
        - (x * x - x + 1#)                       ≈⟨ -‿cong x²-x+1≈0 ⟩
        - 0#                                     ≈⟨ -0≈0 ⟩
        0#
        ∎

      x*y≈1 : x * y ≈ 1#
      x*y≈1 = x-y≈0⇒x≈y x*y-1≈0

  -- 後で定義する _⊛_ の「発散しない場合」の定義
  -- func x y = (xy - 1) / (x + y - 1)
  func : (x y : Carrier) → (x+y#1 : x + y # 1#) → Carrier
  func x y x+y#1 = (x * y - 1#) * proj₁ (#⇒invertible x+y#1)

  func-cong
    : ∀ {x₁ x₂ y₁ y₂} → (x₁+y₁#1 : x₁ + y₁ # 1#) → (x₂+y₂#1 : x₂ + y₂ # 1#)
    → x₁ ≈ x₂ → y₁ ≈ y₂
    → func x₁ y₁ x₁+y₁#1 ≈ func x₂ y₂ x₂+y₂#1
  func-cong {x₁} {x₂} {y₁} {y₂} x₁+y₁#1 x₂+y₂#1 x₁≈x₂ y₁≈y₂ =
    *-cong (+-cong (*-cong x₁≈x₂ y₁≈y₂) refl)
           (unique-inverse (+-cong (+-cong x₁≈x₂ y₁≈y₂) refl) (#⇒invertible x₁+y₁#1) (#⇒invertible x₂+y₂#1))

  func-comm : ∀ x y → (x+y#1 : x + y # 1#) → (y+x#1 : y + x # 1#) → func x y x+y#1 ≈ func y x y+x#1
  func-comm x y x+y#1 y+x#1 = *-cong
    (+-cong (*-comm x y) refl)
    (unique-inverse (+-cong (+-comm x y) refl) (#⇒invertible x+y#1) (#⇒invertible y+x#1))

  -- (x ⊛ y) ⊛ z を「分子/分母」と書いたときに現れる、x, y, z について対称な多項式
  N : Carrier → Carrier → Carrier → Carrier
  N x y z = x * y * z - x - y - z + 1#

  D : Carrier → Carrier → Carrier → Carrier
  D x y z = x * y + x * z + y * z - x - y - z

  N-sym : ∀ x y z → N x y z ≈ N z y x
  N-sym x y z = solve 6
    (λ x y z mx my mz → x :* y :* z :+ mx :+ my :+ mz :+ con 1
                     := z :* y :* x :+ mz :+ my :+ mx :+ con 1)
    refl x y z (- x) (- y) (- z)
    where open Solver

  D-sym : ∀ x y z → D x y z ≈ D z y x
  D-sym x y z = solve 6
    (λ x y z mx my mz → x :* y :+ x :* z :+ y :* z :+ mx :+ my :+ mz
                     := z :* y :+ z :* x :+ y :* x :+ mz :+ my :+ mx)
    refl x y z (- x) (- y) (- z)
    where open Solver

  -- y + z ≈ 1 のとき D x y z は y * z - 1 に簡約される
  D-when-y+z≈1 : ∀ x {y z} → y + z ≈ 1# → D x y z ≈ y * z - 1#
  D-when-y+z≈1 x {y} {z} y+z≈1 = begin
    x * y + x * z + y * z - x - y - z
      ≈⟨ +-cong (+-cong (+-cong refl (sym (-1*x≈-x x))) (sym (-1*x≈-x y))) (sym (-1*x≈-x z)) ⟩
    x * y + x * z + y * z + (- 1#) * x + (- 1#) * y + (- 1#) * z
      ≈⟨ solve 4 (λ x y z m → x :* y :+ x :* z :+ y :* z :+ m :* x :+ m :* y :+ m :* z
                           := x :* (y :+ z) :+ y :* z :+ m :* x :+ m :* (y :+ z))
           refl x y z (- 1#) ⟩
    x * (y + z) + y * z + (- 1#) * x + (- 1#) * (y + z)
      ≈⟨ +-cong (+-cong (+-cong (*-cong refl y+z≈1) refl) refl) (*-cong refl y+z≈1) ⟩
    x * 1# + y * z + (- 1#) * x + (- 1#) * 1#
      ≈⟨ +-cong (+-cong (+-cong (*-identityʳ x) refl) (-1*x≈-x x)) (-1*x≈-x 1#) ⟩
    x + y * z + (- x) + (- 1#)
      ≈⟨ solve 4 (λ a b c m → a :+ b :+ c :+ m := b :+ (a :+ c) :+ m)
           refl x (y * z) (- x) (- 1#) ⟩
    y * z + (x + (- x)) + (- 1#)
      ≈⟨ +-cong (+-cong refl (-‿inverseʳ x)) refl ⟩
    y * z + 0# + (- 1#)
      ≈⟨ +-cong (+-identityʳ _) refl ⟩
    y * z - 1#
    ∎
    where open Solver

  -- 鍵となる多項式恒等式（base 版）：(func x y + z - 1)(x + y - 1) ≈ D x y z
  [func+z-1][x+y-1]≈D
    : ∀ {x y} → (x+y#1 : x + y # 1#) → ∀ z
    → (func x y x+y#1 + z - 1#) * (x + y - 1#) ≈ D x y z
  [func+z-1][x+y-1]≈D {x} {y} x+y#1 z =
    begin
      ((x * y - 1#) * proj₁ (#⇒invertible x+y#1) + z - 1#) * (x + y - 1#)
    ≈⟨ solve 5 (λ a b c d e → (a :* b :+ c :+ d) :* e := a :* (b :* e) :+ c :* e :+ d :* e) refl _ _ _ _ _ ⟩
      (x * y - 1#) * (proj₁ (#⇒invertible x+y#1) * (x + y - 1#)) + z * (x + y - 1#) + (- 1#) * (x + y - 1#)
    ≈⟨ +-cong (+-cong (*-cong refl (proj₁ (proj₂ (#⇒invertible x+y#1)))) refl) refl ⟩
      (x * y - 1#) * 1# + z * (x + y - 1#) + (- 1#) * (x + y - 1#)
    ≈⟨ solve 4 (λ x y z m →
                 (x :* y :+ m) :* con 1 :+ z :* (x :+ y :+ m) :+ m :* (x :+ y :+ m)
                 := x :* y :+ x :* z :+ y :* z :+ m :* x :+ m :* y :+ m :* z :+ (m :* m :+ m)
               ) refl x y z (- 1#) ⟩
      x * y + x * z + y * z + (- 1#) * x + (- 1#) * y + (- 1#) * z + ((- 1#) * (- 1#) + (- 1#))
    ≈⟨ +-cong refl (+-cong -1*-1≈1 refl) ⟩
      x * y + x * z + y * z + (- 1#) * x + (- 1#) * y + (- 1#) * z + (1# + (- 1#))
    ≈⟨ +-cong (+-cong (+-cong (+-cong refl (-1*x≈-x x)) (-1*x≈-x y)) (-1*x≈-x z)) (-‿inverseʳ 1#) ⟩
      x * y + x * z + y * z - x - y - z + 0#
    ≈⟨ +-identityʳ _ ⟩
      x * y + x * z + y * z - x - y - z
    ∎
    where
      open Solver

  -- 派生版：base + +-comm + func-comm + D-sym で従う
  [x+func-1][y+z-1]≈D
    : ∀ x {y z} → (y+z#1 : y + z # 1#)
    → (x + func y z y+z#1 - 1#) * (y + z - 1#) ≈ D x y z
  [x+func-1][y+z-1]≈D x {y} {z} y+z#1 =
    begin
      (x + func y z y+z#1 - 1#) * (y + z - 1#)
    ≈⟨ *-cong (+-cong (+-cong refl (func-comm y z y+z#1 z+y#1)) refl) (+-cong (+-comm y z) refl) ⟩
      (x + func z y z+y#1 - 1#) * (z + y - 1#)
    ≈⟨ *-cong (+-cong (+-comm x (func z y z+y#1)) refl) refl ⟩
      (func z y z+y#1 + x - 1#) * (z + y - 1#)
    ≈⟨ [func+z-1][x+y-1]≈D z+y#1 x ⟩
      D z y x
    ≈⟨ sym (D-sym x y z) ⟩
      D x y z
    ∎
    where
      z+y#1 : z + y # 1#
      z+y#1 = #-congʳ (+-comm y z) y+z#1

  -- 鍵となる多項式恒等式（base 版）：(func x y * z - 1)(x + y - 1) ≈ N x y z
  [func*z-1][x+y-1]≈N
    : ∀ {x y} → (x+y#1 : x + y # 1#) → ∀ z
    → (func x y x+y#1 * z - 1#) * (x + y - 1#) ≈ N x y z
  [func*z-1][x+y-1]≈N {x} {y} x+y#1 z =
    begin
      ((x * y - 1#) * proj₁ (#⇒invertible x+y#1) * z - 1#) * (x + y - 1#)
    ≈⟨ solve 5 (λ p s s⁻¹ z c → (p :* s⁻¹ :* z :+ c) :* s := p :* (s⁻¹ :* s) :* z :+ c :* s)
         refl
         (x * y - 1#) (x + y - 1#) (proj₁ (#⇒invertible x+y#1)) z (- 1#) ⟩
      ((x * y - 1#) * (proj₁ (#⇒invertible x+y#1) * (x + y - 1#)) * z + (- 1#) * (x + y - 1#))
    ≈⟨ +-cong (*-cong (*-cong refl (proj₁ (proj₂ (#⇒invertible x+y#1)))) refl) refl ⟩
      ((x * y - 1#) * 1# * z + (- 1#) * (x + y - 1#))
    ≈⟨ solve 4 (λ x y z m → ((x :* y :+ m) :* con 1 :* z :+ m :* (x :+ y :+ m)) := x :* y :* z :+ m :* x :+ m :* y :+ m :* z :+ m :* m)
         refl x y z (- 1#) ⟩
      x * y * z + (- 1#) * x + (- 1#) * y + (- 1#) * z + (- 1#) * (- 1#)
    ≈⟨ +-cong (+-cong (+-cong (+-cong refl (-1*x≈-x x)) (-1*x≈-x y)) (-1*x≈-x z)) -1*-1≈1 ⟩
      x * y * z - x - y - z + 1#
    ∎
    where
      open Solver

  -- 派生版：base + *-comm + func-comm + N-sym で従う
  [x*func-1][y+z-1]≈N
    : ∀ x {y z} → (y+z#1 : y + z # 1#)
    → (x * func y z y+z#1 - 1#) * (y + z - 1#) ≈ N x y z
  [x*func-1][y+z-1]≈N x {y} {z} y+z#1 =
    begin
      (x * func y z y+z#1 - 1#) * (y + z - 1#)
    ≈⟨ *-cong (+-cong (*-cong refl (func-comm y z y+z#1 z+y#1)) refl) (+-cong (+-comm y z) refl) ⟩
      (x * func z y z+y#1 - 1#) * (z + y - 1#)
    ≈⟨ *-cong (+-cong (*-comm x (func z y z+y#1)) refl) refl ⟩
      (func z y z+y#1 * x - 1#) * (z + y - 1#)
    ≈⟨ [func*z-1][x+y-1]≈N z+y#1 x ⟩
      N z y x
    ≈⟨ sym (N-sym x y z) ⟩
      N x y z
    ∎
    where
      z+y#1 : z + y # 1#
      z+y#1 = #-congʳ (+-comm y z) y+z#1

  func-assoc
    : ∀ x y z
    → (x+y#1 : (x + y # 1#))
    → (y+z#1 : (y + z # 1#))
    → (x⊛y+z#1 : func x y x+y#1 + z # 1#)
    → (x+y⊛z#1 : x + func y z y+z#1 # 1#)
    → func (func x y x+y#1) z x⊛y+z#1 ≈ func x (func y z y+z#1) x+y⊛z#1
  func-assoc x y z x+y#1 y+z#1 x⊛y+z#1 x+y⊛z#1 = invert-both lem (#⇒invertible x+y⊛z#1) (#⇒invertible x⊛y+z#1)
    where
      open Solver

      -- 中央 N(x,y,z) * D(x,y,z) は x↔z で対称なので、両辺は等しい（refl で繋がる）
      lem : (func x y x+y#1 * z   - 1#) * (x + func y z y+z#1 - 1#) ≈ (x * func y z y+z#1 - 1#) * (func x y x+y#1 + z - 1#)
      lem = *-cancelʳ (y + z - 1#) (#⇒invertible y+z#1) $ *-cancelʳ (x + y - 1#) (#⇒invertible x+y#1) $
        begin
          (func x y x+y#1 * z - 1#) * (x + func y z y+z#1 - 1#) * (y + z - 1#) * (x + y - 1#)
        ≈⟨ solve 4 (λ a b c d → a :* b :* c :* d := (a :* d) :* (b :* c)) refl _ _ _ _ ⟩
          (func x y x+y#1 * z - 1#) * (x + y - 1#) * ((x + func y z y+z#1 - 1#) * (y + z - 1#))
        ≈⟨ *-cong ([func*z-1][x+y-1]≈N x+y#1 z) ([x+func-1][y+z-1]≈D x y+z#1) ⟩
          N x y z * D x y z
        ≈⟨ *-cong (sym ([x*func-1][y+z-1]≈N x y+z#1)) (sym ([func+z-1][x+y-1]≈D x+y#1 z)) ⟩
          (x * func y z y+z#1 - 1#)  * (y + z - 1#) * ((func x y x+y#1 + z - 1#) * (x + y - 1#))
        ≈⟨ solve 4 (λ a b c d → (a :* c) :* (b :* d) := a :* b :* c :* d) refl _ _ _ _ ⟩
          (x * func y z y+z#1 - 1#) * (func x y x+y#1 + z - 1#) * (y + z - 1#) * (x + y - 1#)
        ∎

  -- 「結合律の核」：(x+y#1 のとき) func x y + z ≈ 1 ⟺ D x y z ≈ 0
  --   forward: 旧 lemma-3 の役割
  func+z≈1⇒D≈0
    : ∀ {x y} → (x+y#1 : x + y # 1#) → ∀ z
    → func x y x+y#1 + z ≈ 1# → D x y z ≈ 0#
  func+z≈1⇒D≈0 {x} {y} x+y#1 z x⊛y+z≈1 =
    begin
      D x y z
    ≈⟨ sym ([func+z-1][x+y-1]≈D x+y#1 z) ⟩
      (func x y x+y#1 + z - 1#) * (x + y - 1#)
    ≈⟨ *-cong (x≈y⇒x-y≈0 x⊛y+z≈1) refl ⟩
      0# * (x + y - 1#)
    ≈⟨ zeroˡ _ ⟩
      0#
    ∎

  --   backward: 旧 lemma-4 の役割
  D≈0⇒func+z≈1
    : ∀ {x y} → (x+y#1 : x + y # 1#) → ∀ z
    → D x y z ≈ 0# → func x y x+y#1 + z ≈ 1#
  D≈0⇒func+z≈1 {x} {y} x+y#1 z D≈0 = x-y≈0⇒x≈y $
    begin
      func x y x+y#1 + z - 1#
    ≈⟨ sym (*-identityʳ _) ⟩
      (func x y x+y#1 + z - 1#) * 1#
    ≈⟨ *-cong refl (sym (proj₂ (proj₂ (#⇒invertible x+y#1)))) ⟩
      (func x y x+y#1 + z - 1#) * ((x + y - 1#) * proj₁ (#⇒invertible x+y#1))
    ≈⟨ sym (*-assoc _ _ _) ⟩
      (func x y x+y#1 + z - 1#) * (x + y - 1#) * proj₁ (#⇒invertible x+y#1)
    ≈⟨ *-cong ([func+z-1][x+y-1]≈D x+y#1 z) refl ⟩
      D x y z * proj₁ (#⇒invertible x+y#1)
    ≈⟨ *-cong D≈0 refl ⟩
      0# * proj₁ (#⇒invertible x+y#1)
    ≈⟨ zeroˡ _ ⟩
      0#
    ∎

  --   forward (右ずらし版): 旧 lemma-3' の役割
  x+func≈1⇒D≈0
    : ∀ x {y z} → (y+z#1 : y + z # 1#)
    → x + func y z y+z#1 ≈ 1# → D x y z ≈ 0#
  x+func≈1⇒D≈0 x {y} {z} y+z#1 x+y⊛z≈1 =
    begin
      D x y z
    ≈⟨ sym ([x+func-1][y+z-1]≈D x y+z#1) ⟩
      (x + func y z y+z#1 - 1#) * (y + z - 1#)
    ≈⟨ *-cong (x≈y⇒x-y≈0 x+y⊛z≈1) refl ⟩
      0# * (y + z - 1#)
    ≈⟨ zeroˡ _ ⟩
      0#
    ∎

  --   backward (右ずらし版): 旧 lemma-4' の役割
  D≈0⇒x+func≈1
    : ∀ x {y z} → (y+z#1 : y + z # 1#)
    → D x y z ≈ 0# → x + func y z y+z#1 ≈ 1#
  D≈0⇒x+func≈1 x {y} {z} y+z#1 D≈0 = x-y≈0⇒x≈y $
    begin
      x + func y z y+z#1 - 1#
    ≈⟨ sym (*-identityʳ _) ⟩
      (x + func y z y+z#1 - 1#) * 1#
    ≈⟨ *-cong refl (sym (proj₂ (proj₂ (#⇒invertible y+z#1)))) ⟩
      (x + func y z y+z#1 - 1#) * ((y + z - 1#) * proj₁ (#⇒invertible y+z#1))
    ≈⟨ sym (*-assoc _ _ _) ⟩
      (x + func y z y+z#1 - 1#) * (y + z - 1#) * proj₁ (#⇒invertible y+z#1)
    ≈⟨ *-cong ([x+func-1][y+z-1]≈D x y+z#1) refl ⟩
      D x y z * proj₁ (#⇒invertible y+z#1)
    ≈⟨ *-cong D≈0 refl ⟩
      0# * proj₁ (#⇒invertible y+z#1)
    ≈⟨ zeroˡ _ ⟩
      0#
    ∎

  -- y + z ≈ 1 のとき N(x, y, z) は x * D(x, y, z) に等しい（[func[func]z]≈x の核となる代数的事実）
  N≈x*D-when-y+z≈1
    : ∀ x {y z} → y + z ≈ 1# → N x y z ≈ x * D x y z
  N≈x*D-when-y+z≈1 x {y} {z} y+z≈1 = begin
    x * y * z - x - y - z + 1#
      ≈⟨ +-cong (+-cong (+-cong (+-cong refl (sym (-1*x≈-x x))) (sym (-1*x≈-x y))) (sym (-1*x≈-x z))) refl ⟩
    x * y * z + (- 1#) * x + (- 1#) * y + (- 1#) * z + 1#
      ≈⟨ solve 4 (λ x y z m →
                     x :* y :* z :+ m :* x :+ m :* y :+ m :* z :+ con 1
                     := x :* y :* z :+ m :* x :+ m :* (y :+ z) :+ con 1)
           refl x y z (- 1#) ⟩
    x * y * z + (- 1#) * x + (- 1#) * (y + z) + 1#
      ≈⟨ +-cong (+-cong refl (*-cong refl y+z≈1)) refl ⟩
    x * y * z + (- 1#) * x + (- 1#) * 1# + 1#
      ≈⟨ +-cong (+-cong (+-cong refl (-1*x≈-x x)) (-1*x≈-x 1#)) refl ⟩
    x * y * z + (- x) + (- 1#) + 1#
      ≈⟨ +-assoc _ _ _ ⟩
    x * y * z + (- x) + (- 1# + 1#)
      ≈⟨ +-cong refl (-‿inverseˡ 1#) ⟩
    x * y * z + (- x) + 0#
      ≈⟨ +-identityʳ _ ⟩
    x * y * z + (- x)
      ≈⟨ +-cong refl (sym (-1*x≈-x x)) ⟩
    x * y * z + (- 1#) * x
      ≈⟨ +-cong refl (*-comm (- 1#) x) ⟩
    x * y * z + x * (- 1#)
      ≈⟨ +-cong (*-assoc x y z) refl ⟩
    x * (y * z) + x * (- 1#)
      ≈⟨ sym (distribˡ x (y * z) (- 1#)) ⟩
    x * (y * z - 1#)
      ≈⟨ *-cong refl (sym (D-when-y+z≈1 x y+z≈1)) ⟩
    x * D x y z
    ∎
    where open Solver

  -- 旧 lemma-2 の改名: y + z ≈ 1 のとき (x ⊛ y) ⊛ z = x （その func 部分が x）
  [func[func]z]≈x-when-y+z≈1
    : ∀ {x y z} → (x+y#1 : x + y # 1#) → ¬ (y + z # 1#) → (x⊛y+z#1 : func x y x+y#1 + z # 1#)
    → func (func x y x+y#1) z x⊛y+z#1 ≈ x
  [func[func]z]≈x-when-y+z≈1 {x} {y} {z} x+y#1 ¬y+z#1 x⊛y+z#1 =
    *-cancelʳ (func x y x+y#1 + z - 1#) (#⇒invertible x⊛y+z#1) $
    *-cancelʳ (x + y - 1#) (#⇒invertible x+y#1) $ lem
    where
      y+z≈1 : y + z ≈ 1#
      y+z≈1 = proj₁ (tight _ _) ¬y+z#1

      lem : func (func x y x+y#1) z x⊛y+z#1 * (func x y x+y#1 + z - 1#) * (x + y - 1#)
            ≈ x * (func x y x+y#1 + z - 1#) * (x + y - 1#)
      lem = begin
          func (func x y x+y#1) z x⊛y+z#1 * (func x y x+y#1 + z - 1#) * (x + y - 1#)
        ≈⟨ refl ⟩
          (func x y x+y#1 * z - 1#) * proj₁ (#⇒invertible x⊛y+z#1) * (func x y x+y#1 + z - 1#) * (x + y - 1#)
        ≈⟨ *-cong (*-assoc _ _ _) refl ⟩
          (func x y x+y#1 * z - 1#) * (proj₁ (#⇒invertible x⊛y+z#1) * (func x y x+y#1 + z - 1#)) * (x + y - 1#)
        ≈⟨ *-cong (*-cong refl (proj₁ (proj₂ (#⇒invertible x⊛y+z#1)))) refl ⟩
          (func x y x+y#1 * z - 1#) * 1# * (x + y - 1#)
        ≈⟨ *-cong (*-identityʳ _) refl ⟩
          (func x y x+y#1 * z - 1#) * (x + y - 1#)
        ≈⟨ [func*z-1][x+y-1]≈N x+y#1 z ⟩
          N x y z
        ≈⟨ N≈x*D-when-y+z≈1 x y+z≈1 ⟩
          x * D x y z
        ≈⟨ *-cong refl (sym ([func+z-1][x+y-1]≈D x+y#1 z)) ⟩
          x * ((func x y x+y#1 + z - 1#) * (x + y - 1#))
        ≈⟨ sym (*-assoc _ _ _) ⟩
          x * (func x y x+y#1 + z - 1#) * (x + y - 1#)
        ∎

  -- 旧 lemma-1 の改名・簡素化: y + z ≈ 1 かつ func x y + z ≈ 1 ならば、(y, z) は禁止条件 (y+z=1) ∧ (yz=1) を満たす
  bad-pair-when-y+z≈1
    : ∀ {x y z} → (x+y#1 : x + y # 1#) → ¬ (y + z # 1#) → ¬ (func x y x+y#1 + z # 1#)
    → (y + z ≈ 1#) × (y * z ≈ 1#)
  bad-pair-when-y+z≈1 {x} {y} {z} x+y#1 ¬y+z#1 ¬x⊛y+z#1 = (y+z≈1 , y*z≈1)
    where
      y+z≈1 : y + z ≈ 1#
      y+z≈1 = proj₁ (tight _ _) ¬y+z#1

      x⊛y+z≈1 : func x y x+y#1 + z ≈ 1#
      x⊛y+z≈1 = proj₁ (tight _ _) ¬x⊛y+z#1

      D≈0 : D x y z ≈ 0#
      D≈0 = func+z≈1⇒D≈0 x+y#1 z x⊛y+z≈1

      yz-1≈0 : y * z - 1# ≈ 0#
      yz-1≈0 = trans (sym (D-when-y+z≈1 x y+z≈1)) D≈0

      y*z≈1 : y * z ≈ 1#
      y*z≈1 = x-y≈0⇒x≈y yz-1≈0

open Utils

open HeytingField HF
  renaming
  ( Carrier       to F
  ; _≈_           to _≈F_
  ; isEquivalence to F-isEquivalence
  ; setoid        to F-setoid
  )

open IsEquivalence F-isEquivalence
  renaming
  ( refl  to F-refl
  ; sym   to F-sym
  ; trans to F-trans
  )

open import Algebra.Apartness.Properties.HeytingCommutativeRing (heytingCommutativeRing)

module F-Solver = Algebra.Solver.Ring.NaturalCoefficients.Default
  (CommutativeRing.commutativeSemiring (HeytingCommutativeRing.commutativeRing heytingCommutativeRing))

data E : Set c where
  fin : F → E
  ∞ : E

infix  4 _≈_

data _≈_ : Rel E (c ⊔ ℓ₁) where
  ∞≈∞ : ∞ ≈ ∞
  fin-cong : {x y : F} → x ≈F y → fin x ≈ fin y

≈-refl : Reflexive _≈_
≈-refl {∞} = ∞≈∞
≈-refl {fin x} = fin-cong F-refl

≈-sym : Symmetric _≈_
≈-sym ∞≈∞ = ∞≈∞
≈-sym (fin-cong x≈y) = fin-cong (F-sym x≈y)

≈-trans : Transitive _≈_
≈-trans ∞≈∞ ∞≈∞ = ∞≈∞
≈-trans (fin-cong x≈y) (fin-cong y≈z) = fin-cong (F-trans x≈y y≈z)

≈-isEquivalence : IsEquivalence (_≈_)
≈-isEquivalence = record
  { refl = ≈-refl
  ; sym = ≈-sym
  ; trans = ≈-trans
  }

setoid : Setoid c (c ⊔ ℓ₁)
setoid = record
  { Carrier = E
  ; _≈_ = _≈_
  ; isEquivalence = ≈-isEquivalence
  }

infixl 7 _⊛_

-- x ⊛ y = (xy - 1) / (x + y - 1)
_⊛_ : E → E → E
∞ ⊛ y = y
x ⊛ ∞ = x
fin x ⊛ fin y with #-dec (x + y) 1#
... | yes x+y#1 = fin (func x y x+y#1)
... | no _ = ∞

⊛-identityˡ : LeftIdentity (_≈_) ∞ _⊛_
⊛-identityˡ x = ≈-refl

⊛-identityʳ : RightIdentity (_≈_) ∞ _⊛_
⊛-identityʳ ∞ = ≈-refl
⊛-identityʳ (fin x) = ≈-refl

⊛-comm : Commutative (_≈_) _⊛_
⊛-comm ∞ y = begin
  ∞ ⊛ y  ≈⟨ ⊛-identityˡ y ⟩
  y      ≈⟨ ≈-sym (⊛-identityʳ y) ⟩
  y ⊛ ∞
  ∎
  where open ≈-Reasoning setoid
⊛-comm x ∞ = begin
  x ⊛ ∞   ≈⟨ ⊛-identityʳ x ⟩
  x       ≈⟨ ≈-sym (⊛-identityˡ x) ⟩
  ∞ ⊛ x
  ∎
  where open ≈-Reasoning setoid
⊛-comm (fin x) (fin y) with #-dec (x + y) 1# | #-dec (y + x) 1#
... | yes x+y#1 | yes y+x#1 = fin-cong $ func-comm x y x+y#1 y+x#1
... | yes x+y#1 | no ¬y+x#1 = ⊥-elim (¬y+x#1 (#-congʳ (+-comm x y) x+y#1))
... | no ¬x+y#1 | yes y+x#1 = ⊥-elim (¬x+y#1 (#-congʳ (+-comm y x) y+x#1))
... | no ¬x+y#1 | no ¬y+x#1 = ∞≈∞

⊛-cong : Congruent₂ (_≈_) _⊛_
⊛-cong ∞≈∞ y₁≈y₂ = y₁≈y₂
⊛-cong {x₁} {x₂} x₁≈x₂ ∞≈∞ = begin
  x₁ ⊛ ∞  ≈⟨ ⊛-identityʳ x₁ ⟩
  x₁      ≈⟨ x₁≈x₂ ⟩
  x₂      ≈⟨ ≈-sym (⊛-identityʳ x₂) ⟩
  x₂ ⊛ ∞
  ∎
  where open ≈-Reasoning setoid
⊛-cong (fin-cong {x₁} {x₂} x₁≈x₂) (fin-cong {y₁} {y₂} y₁≈y₂) with #-dec (x₁ + y₁) 1# | #-dec (x₂ + y₂) 1#
... | yes x₁+y₁#1 | yes x₂+y₂#1 = fin-cong $ *-cong
  (+-cong (*-cong x₁≈x₂ y₁≈y₂) F-refl)
  (unique-inverse r (#⇒invertible x₁+y₁#1) ((#⇒invertible x₂+y₂#1)))
  where
    r : (x₁ + y₁) - 1# ≈F (x₂ + y₂) - 1#
    r = +-cong (+-cong x₁≈x₂ y₁≈y₂) F-refl
... | yes x₁+y₁#1 | no ¬x₂+y₂#1 = ⊥-elim (¬x₂+y₂#1 (#-congʳ (+-cong x₁≈x₂ y₁≈y₂) x₁+y₁#1))
... | no ¬x₁+y₁#1 | yes x₂+y₂#1 = ⊥-elim (¬x₁+y₁#1 (#-congʳ (+-cong (F-sym x₁≈x₂) (F-sym y₁≈y₂)) x₂+y₂#1))
... | no ¬x₁+y₁#1 | no ¬x₂+y₂#1 = ∞≈∞

isMagma : IsMagma _≈_ _⊛_
isMagma = record
  { isEquivalence = ≈-isEquivalence
  ; ∙-cong = ⊛-cong
  }

_⁻¹ : E → E
∞ ⁻¹ = ∞
(fin x) ⁻¹ = fin (1# - x)

isLeftInverse : LeftInverse _≈_ ∞ (_⁻¹) _⊛_
isLeftInverse ∞ = ∞≈∞
isLeftInverse (fin x) with #-dec ((1# - x) + x) 1#
... | yes 1-x+x#1 = ⊥-elim (lem3 lem2)
  where
    lem1 : 1# - x + x ≈F 1#
    lem1 = begin
      (1# - x) + x    ≈⟨ +-assoc 1# (- x) x ⟩
      1# + (- x + x)  ≈⟨ +-cong F-refl (-‿inverseˡ x) ⟩
      1# + 0#         ≈⟨ +-identityʳ 1# ⟩
      1#
      ∎
      where open ≈-Reasoning F-setoid
    lem2 : 1# # 1#
    lem2 = #-congʳ lem1 1-x+x#1
    lem3 : ¬ (1# # 1#)
    lem3 = proj₂ (tight 1# 1#) F-refl
... | no ¬1-x+x#1 = ∞≈∞

isRightInverse : RightInverse _≈_ ∞ (_⁻¹) _⊛_
isRightInverse x = begin
  x ⊛ (x ⁻¹)  ≈⟨ ⊛-comm x (x ⁻¹) ⟩
  (x ⁻¹) ⊛ x  ≈⟨ isLeftInverse x ⟩
  ∞
  ∎
  where open ≈-Reasoning setoid

⁻¹-cong : Congruent₁ _≈_ _⁻¹
⁻¹-cong {.∞} {.∞} (∞≈∞) = ∞≈∞
⁻¹-cong {.fin x} {.fin y} (fin-cong {x} {y} x≈y) = fin-cong (+-cong F-refl (-‿cong x≈y))

module Main (condition : ∀ {x y} → ¬ ((x + y ≈F 1#) × (x * y ≈F 1#))) where

  ⊛-fin-assoc : (x y z : F) → (fin x ⊛ fin y) ⊛ fin z ≈ fin x ⊛ (fin y ⊛ fin z)
  ⊛-fin-assoc x y z with #-dec (x + y) 1# | #-dec (y + z) 1#
  ⊛-fin-assoc x y z | yes x+y#1 | yes y+z#1 with #-dec (func x y x+y#1 + z) 1# | #-dec (x + func y z y+z#1) 1#
  ⊛-fin-assoc x y z | yes x+y#1 | yes y+z#1 | yes x⊛y+z#1 | yes x+y⊛z#1 = fin-cong (func-assoc x y z x+y#1 y+z#1 x⊛y+z#1 x+y⊛z#1)
  ⊛-fin-assoc x y z | yes x+y#1 | yes y+z#1 | yes x⊛y+z#1 | no ¬x+y⊛z#1 = ⊥-elim ((¬x⊛y+z#1 x⊛y+z#1))
    where
      D≈0 : D x y z ≈F 0#
      D≈0 = x+func≈1⇒D≈0 x y+z#1 (proj₁ (tight _ _) (¬x+y⊛z#1))

      x⊛y+z≈1 : func x y x+y#1 + z ≈F 1#
      x⊛y+z≈1 = D≈0⇒func+z≈1 x+y#1 z D≈0

      ¬x⊛y+z#1 : ¬ (func x y x+y#1 + z # 1#)
      ¬x⊛y+z#1 = proj₂ (tight _ _) x⊛y+z≈1

  ⊛-fin-assoc x y z | yes x+y#1 | yes y+z#1 | no ¬x⊛y+z#1 | yes x+y⊛z#1 = ⊥-elim (¬x+y⊛z#1 x+y⊛z#1)
    where
      D≈0 : D x y z ≈F 0#
      D≈0 = func+z≈1⇒D≈0 x+y#1 z (proj₁ (tight _ _) (¬x⊛y+z#1))

      x+y⊛z≈1 : x + func y z y+z#1 ≈F 1#
      x+y⊛z≈1 = D≈0⇒x+func≈1 x y+z#1 D≈0

      ¬x+y⊛z#1 : ¬ (x + func y z y+z#1 # 1#)
      ¬x+y⊛z#1 = proj₂ (tight _ _) x+y⊛z≈1

  ⊛-fin-assoc x y z | yes x+y#1 | yes y+z#1 | no ¬x⊛y+z#1 | no ¬x+y⊛z#1 = ∞≈∞
  ⊛-fin-assoc x y z | yes x+y#1 | no ¬y+z#1 with #-dec (func x y x+y#1 + z) 1#
  ⊛-fin-assoc x y z | yes x+y#1 | no ¬y+z#1 | yes x⊛y+z#1 = fin-cong ([func[func]z]≈x-when-y+z≈1 x+y#1 ¬y+z#1 x⊛y+z#1)
  ⊛-fin-assoc x y z | yes x+y#1 | no ¬y+z#1 | no ¬x⊛y+z#1 = ⊥-elim (condition (bad-pair-when-y+z≈1 x+y#1 ¬y+z#1 ¬x⊛y+z#1))
  ⊛-fin-assoc x y z | no ¬x+y#1 | yes y+z#1 with #-dec (x + func y z y+z#1) 1#
  ⊛-fin-assoc x y z | no ¬x+y#1 | yes y+z#1 | yes x+y⊛z#1 = fin-cong (F-sym lem)
    where
      open ≈-Reasoning F-setoid

      z+y#1 : z + y # 1#
      z+y#1 = #-congʳ (+-comm _ _) y+z#1

      ¬y+x#1 : ¬ (y + x # 1#)
      ¬y+x#1 y+x#1 = ¬x+y#1 (#-congʳ (+-comm _ _) y+x#1)

      y⊛z+x#1 : func y z y+z#1 + x # 1#
      y⊛z+x#1 = #-congʳ (+-comm _ _) x+y⊛z#1

      z⊛y+x#1 : func z y z+y#1 + x # 1#
      z⊛y+x#1 = #-congʳ (+-cong (func-comm y z y+z#1 z+y#1) (refl {x})) y⊛z+x#1

      lem : func x (func y z y+z#1) x+y⊛z#1 ≈F z
      lem = begin
        func x (func y z y+z#1) x+y⊛z#1  ≈⟨ func-comm x ((func y z y+z#1)) x+y⊛z#1 y⊛z+x#1 ⟩
        func (func y z y+z#1) x y⊛z+x#1  ≈⟨ func-cong y⊛z+x#1 z⊛y+x#1 (func-comm y z y+z#1 z+y#1) refl ⟩
        func (func z y z+y#1) x z⊛y+x#1  ≈⟨ [func[func]z]≈x-when-y+z≈1 z+y#1 ¬y+x#1 z⊛y+x#1 ⟩
        z
        ∎

  ⊛-fin-assoc x y z | no ¬x+y#1 | yes y+z#1 | no ¬x+y⊛z#1 = ⊥-elim (condition (bad-pair-when-y+z≈1 z+y#1 ¬y+x#1 ¬z⊛y+x#1))
    where
      open ≈-Reasoning F-setoid

      z+y#1 : z + y # 1#
      z+y#1 = #-congʳ (+-comm _ _) y+z#1

      ¬y+x#1 : ¬ (y + x # 1#)
      ¬y+x#1 y+x#1 = ¬x+y#1 (#-congʳ (+-comm _ _) y+x#1)

      z⊛y+x≈x+y⊛z : func z y z+y#1 + x ≈F x + func y z y+z#1
      z⊛y+x≈x+y⊛z = begin
        func z y z+y#1 + x  ≈⟨ +-comm (func z y z+y#1) x ⟩
        x + func z y z+y#1  ≈⟨ +-cong (refl {x}) (func-comm z y z+y#1 y+z#1) ⟩
        x + func y z y+z#1
        ∎

      ¬z⊛y+x#1 : ¬ (func z y z+y#1 + x # 1#)
      ¬z⊛y+x#1 z⊛y+x#1 = ¬x+y⊛z#1 (#-congʳ z⊛y+x≈x+y⊛z z⊛y+x#1)

  ⊛-fin-assoc x y z | no ¬x+y#1 | no ¬y+z#1 = fin-cong z≈x
    where
      open ≈-Reasoning F-setoid

      y+z≈y+x : y + z ≈F y + x
      y+z≈y+x = begin
        y + z  ≈⟨ proj₁ (tight _ _) ¬y+z#1 ⟩
        1#     ≈⟨ F-sym (proj₁ (tight _ _) ¬x+y#1 ) ⟩
        x + y  ≈⟨ +-comm x y ⟩
        y + x
        ∎

      z≈x : z ≈F x
      z≈x = begin
        z              ≈⟨ F-sym (+-identityˡ z) ⟩
        0# + z         ≈⟨ +-cong (F-sym (-‿inverseˡ y)) F-refl ⟩
        (- y + y) + z  ≈⟨ +-assoc (- y) y z ⟩
        - y + (y + z)  ≈⟨ +-cong F-refl y+z≈y+x ⟩
        - y + (y + x)  ≈⟨ F-sym (+-assoc (- y) y x) ⟩
        (- y + y) + x  ≈⟨ +-cong (-‿inverseˡ y) F-refl ⟩
        0# + x         ≈⟨ +-identityˡ x ⟩
        x
        ∎

  ⊛-assoc : Associative _≈_ _⊛_
  ⊛-assoc ∞ y z = ≈-refl
  ⊛-assoc x ∞ z = ⊛-cong (⊛-identityʳ x) ≈-refl
  ⊛-assoc x y ∞ = begin
    ((x ⊛ y) ⊛ ∞)  ≈⟨ ⊛-identityʳ (x ⊛ y) ⟩
    x ⊛ y          ≈⟨ ⊛-cong (≈-refl {x}) (≈-sym (⊛-identityʳ y)) ⟩
    x ⊛ (y ⊛ ∞)
    ∎
    where open ≈-Reasoning setoid
  ⊛-assoc (fin x) (fin y) (fin z) = ⊛-fin-assoc x y z

  isSemigroup : IsSemigroup _≈_ _⊛_
  isSemigroup = record
    { isMagma = isMagma
    ; assoc = ⊛-assoc
    }

  isMonoid : IsMonoid _≈_ _⊛_ ∞
  isMonoid = record
    { isSemigroup = isSemigroup
    ; identity = (⊛-identityˡ , ⊛-identityʳ)
    }

  isGroup : IsGroup _≈_ _⊛_ ∞ (_⁻¹)
  isGroup = record
    { isMonoid = isMonoid
    ; inverse = (isLeftInverse , isRightInverse)
    ; ⁻¹-cong = ⁻¹-cong
    }
