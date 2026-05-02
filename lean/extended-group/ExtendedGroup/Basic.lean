import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic

/-!
# 体 F が x + y = 1 ∧ xy = 1 を満たす元を持たないとき、F ∪ {∞} は群

演算 `_⊛_`:
- `∞ ⊛ y = y`
- `x ⊛ ∞ = x`
- `x ⊛ y = (xy − 1)/(x + y − 1)` if `x + y ≠ 1`
- `x ⊛ y = ∞` otherwise

参考: <https://x.com/MurakamiMath/status/1837434653634187342>
-/

namespace ExtendedGroup

variable {F : Type*} [Field F]

/-! ## §1 中核となる多項式と対称性 -/

/-- `(x ⊛ y)` の発散しない場合の値: `(xy − 1)/(x + y − 1)` -/
def op (x y : F) : F := (x * y - 1) / (x + y - 1)

lemma op_comm (x y : F) : op x y = op y x := by
  unfold op; rw [mul_comm x y, add_comm x y]

/-- `(x ⊛ y) ⊛ z` を有理形にしたときの分子。`x, y, z` について対称。 -/
def N (x y z : F) : F := x * y * z - x - y - z + 1

/-- `(x ⊛ y) ⊛ z` を有理形にしたときの分母。`x, y, z` について対称。 -/
def D (x y z : F) : F := x * y + x * z + y * z - x - y - z

lemma N_swap (x y z : F) : N x y z = N z y x := by unfold N; ring
lemma D_swap (x y z : F) : D x y z = D z y x := by unfold D; ring

/-- `y + z = 1` のとき `D x y z = y * z - 1` -/
lemma D_of_add_eq_one (x : F) {y z : F} (h : y + z = 1) :
    D x y z = y * z - 1 := by
  unfold D
  linear_combination (x - 1) * h

/-- `y + z = 1` のとき `N x y z = x * D x y z` -/
lemma N_eq_mul_D_of_add_eq_one (x : F) {y z : F} (h : y + z = 1) :
    N x y z = x * D x y z := by
  unfold N D
  linear_combination (-x^2 + x - 1) * h

/-! ## §2 鍵となる多項式恒等式 -/

/-- 基本版: `(op x y + z - 1)(x + y - 1) = D x y z` -/
lemma op_add_factor_D {x y : F} (hxy : x + y ≠ 1) (z : F) :
    (op x y + z - 1) * (x + y - 1) = D x y z := by
  unfold op D
  have : x + y - 1 ≠ 0 := sub_ne_zero.mpr hxy
  field_simp
  ring

/-- 基本版: `(op x y * z - 1)(x + y - 1) = N x y z` -/
lemma op_mul_factor_N {x y : F} (hxy : x + y ≠ 1) (z : F) :
    (op x y * z - 1) * (x + y - 1) = N x y z := by
  unfold op N
  have : x + y - 1 ≠ 0 := sub_ne_zero.mpr hxy
  field_simp
  ring

/-- 右ずらし版: `(x + op y z - 1)(y + z - 1) = D x y z` -/
lemma op_add_factor_D' {y z : F} (hyz : y + z ≠ 1) (x : F) :
    (x + op y z - 1) * (y + z - 1) = D x y z := by
  unfold op D
  have : y + z - 1 ≠ 0 := sub_ne_zero.mpr hyz
  field_simp
  ring

/-- 右ずらし版: `(x * op y z - 1)(y + z - 1) = N x y z` -/
lemma op_mul_factor_N' {y z : F} (hyz : y + z ≠ 1) (x : F) :
    (x * op y z - 1) * (y + z - 1) = N x y z := by
  unfold op N
  have : y + z - 1 ≠ 0 := sub_ne_zero.mpr hyz
  field_simp
  ring

/-! ## §3 結合律の核: 同値 `op x y + z = 1 ⟺ D x y z = 0` -/

lemma op_add_eq_one_iff {x y : F} (hxy : x + y ≠ 1) (z : F) :
    op x y + z = 1 ↔ D x y z = 0 := by
  have hne : x + y - 1 ≠ 0 := sub_ne_zero.mpr hxy
  rw [show D x y z = (op x y + z - 1) * (x + y - 1) from (op_add_factor_D hxy z).symm,
      mul_eq_zero, sub_eq_zero, or_iff_left hne]

lemma add_op_eq_one_iff {y z : F} (hyz : y + z ≠ 1) (x : F) :
    x + op y z = 1 ↔ D x y z = 0 := by
  have hne : y + z - 1 ≠ 0 := sub_ne_zero.mpr hyz
  rw [show D x y z = (x + op y z - 1) * (y + z - 1) from (op_add_factor_D' hyz x).symm,
      mul_eq_zero, sub_eq_zero, or_iff_left hne]

/-! ## §4 `y + z = 1` のときの補助補題 -/

/-- `y + z = 1 ∧ op x y + z = 1` ⟹ `(y, z)` は禁止条件を満たす -/
lemma bad_pair_when_y_z_eq_one {x y z : F} (hxy : x + y ≠ 1)
    (hyz : y + z = 1) (h_op : op x y + z = 1) :
    y + z = 1 ∧ y * z = 1 := by
  refine ⟨hyz, ?_⟩
  have hD : D x y z = 0 := (op_add_eq_one_iff hxy z).mp h_op
  have hD' : D x y z = y * z - 1 := D_of_add_eq_one x hyz
  linear_combination hD - hD'

/-- `y + z = 1` のとき `op (op x y) z = x` -/
lemma op_op_eq_left_when_y_z_eq_one {x y z : F} (hxy : x + y ≠ 1)
    (hyz : y + z = 1) (h_op : op x y + z ≠ 1) :
    op (op x y) z = x := by
  have hxy' : x + y - 1 ≠ 0 := sub_ne_zero.mpr hxy
  have h_op' : op x y + z - 1 ≠ 0 := sub_ne_zero.mpr h_op
  change (op x y * z - 1) / (op x y + z - 1) = x
  rw [div_eq_iff h_op']
  have eN := op_mul_factor_N hxy z
  have eD := op_add_factor_D hxy z
  have eND := N_eq_mul_D_of_add_eq_one x hyz
  have key : (op x y * z - 1) * (x + y - 1) = x * (op x y + z - 1) * (x + y - 1) := by
    linear_combination eN + eND - x * eD
  exact mul_right_cancel₀ hxy' key

/-! ## §5 結合律 (F 上、すべての場合分岐が「発散しない」とき) -/

lemma op_assoc {x y z : F} (hxy : x + y ≠ 1) (hyz : y + z ≠ 1)
    (h1 : op x y + z ≠ 1) (h2 : x + op y z ≠ 1) :
    op (op x y) z = op x (op y z) := by
  have hxy' : x + y - 1 ≠ 0 := sub_ne_zero.mpr hxy
  have hyz' : y + z - 1 ≠ 0 := sub_ne_zero.mpr hyz
  have h1' : op x y + z - 1 ≠ 0 := sub_ne_zero.mpr h1
  have h2' : x + op y z - 1 ≠ 0 := sub_ne_zero.mpr h2
  change (op x y * z - 1) / (op x y + z - 1) = (x * op y z - 1) / (x + op y z - 1)
  rw [div_eq_div_iff h1' h2']
  apply mul_right_cancel₀ (mul_ne_zero hxy' hyz')
  -- 中央が N x y z * D x y z という対称形になる
  have eN  := op_mul_factor_N hxy z
  have eD  := op_add_factor_D hxy z
  have eN' := op_mul_factor_N' hyz x
  have eD' := op_add_factor_D' hyz x
  linear_combination
    (x + op y z - 1) * (y + z - 1) * eN + N x y z * eD'
    - (op x y + z - 1) * (x + y - 1) * eN' - N x y z * eD

/-! ## §6 `Option F` 上の演算 -/

/-- 体 F が「禁止条件」を満たさない: `x + y = 1 ∧ x*y = 1` を満たす元を持たない -/
class NoBadPair (F : Type*) [Field F] : Prop where
  no_root : ∀ x y : F, ¬ (x + y = 1 ∧ x * y = 1)

namespace OptionExt

open Classical in
/-- `Option F` 上の演算。`none` が ∞ を表す。 -/
noncomputable def emul : Option F → Option F → Option F
  | none, y => y
  | some x, none => some x
  | some x, some y => if x + y = 1 then none else some (op x y)

/-- 逆元 -/
def einv : Option F → Option F
  | none => none
  | some x => some (1 - x)

@[simp] lemma none_emul (y : Option F) : emul none y = y := rfl

@[simp] lemma emul_none : ∀ x : Option F, emul x none = x
  | none => rfl
  | some _ => rfl

open Classical in
lemma emul_some_some (x y : F) :
    emul (some x) (some y) = if x + y = 1 then none else some (op x y) := rfl

@[simp] lemma einv_none : einv (none : Option F) = none := rfl
@[simp] lemma einv_some (x : F) : einv (some x : Option F) = some (1 - x) := rfl

lemma emul_comm : ∀ (x y : Option F), emul x y = emul y x
  | none, none => rfl
  | none, some _ => rfl
  | some _, none => rfl
  | some x, some y => by
    classical
    simp only [emul_some_some]
    by_cases h : x + y = 1
    · rw [if_pos h, if_pos (by linear_combination h : y + x = 1)]
    · have h' : y + x ≠ 1 := fun h' => h (by linear_combination h')
      rw [if_neg h, if_neg h', op_comm]

lemma einv_emul_self : ∀ (x : Option F), emul (einv x) x = none
  | none => rfl
  | some x => by
    classical
    change (if (1 - x) + x = 1 then (none : Option F) else some (op (1 - x) x)) = none
    rw [if_pos (by ring : (1 - x) + x = 1)]

/-- 結合律 (Option F 上) -/
lemma emul_assoc [NoBadPair F] : ∀ (x y z : Option F),
    emul (emul x y) z = emul x (emul y z)
  | none, _, _ => by simp
  | some _, none, _ => by simp
  | some _, some _, none => by simp
  | some x, some y, some z => by
    classical
    by_cases hxy : x + y = 1
    · -- ケース A or B: x + y = 1
      rw [show emul (some x) (some y) = none from by rw [emul_some_some, if_pos hxy]]
      rw [none_emul]
      by_cases hyz : y + z = 1
      · -- ケース A (x+y=1, y+z=1): z = x
        rw [show emul (some y) (some z) = none from by rw [emul_some_some, if_pos hyz]]
        rw [emul_none]
        congr 1
        linear_combination hyz - hxy
      · -- ケース B (x+y=1, y+z≠1)
        rw [show emul (some y) (some z) = some (op y z) from by
              rw [emul_some_some, if_neg hyz]]
        rw [emul_some_some]
        by_cases h2 : x + op y z = 1
        · -- B1: 矛盾 (x*y=1 が導かれ NoBadPair に反する)
          exfalso
          have hD : D x y z = 0 := (add_op_eq_one_iff hyz x).mp h2
          have hD' : D x y z = x * y - 1 := by
            unfold D; linear_combination (z - 1) * hxy
          have hxy1 : x * y = 1 := by linear_combination hD - hD'
          exact NoBadPair.no_root x y ⟨hxy, hxy1⟩
        · -- B2: z = op x (op y z) を可換性 + lemma-2 で
          rw [if_neg h2]
          congr 1
          have h_zy : z + y ≠ 1 := fun h => hyz (by linear_combination h)
          have h_yx : y + x = 1 := by linear_combination hxy
          have h_zyx : op z y + x ≠ 1 := by
            rw [op_comm z y]; exact fun h => h2 (by linear_combination h)
          have step : op (op z y) x = z := op_op_eq_left_when_y_z_eq_one h_zy h_yx h_zyx
          rw [op_comm x (op y z), op_comm y z]
          exact step.symm
    · -- ケース C or D: x + y ≠ 1
      rw [show emul (some x) (some y) = some (op x y) from by
            rw [emul_some_some, if_neg hxy]]
      by_cases hyz : y + z = 1
      · -- ケース C (x+y≠1, y+z=1)
        rw [show emul (some y) (some z) = none from by rw [emul_some_some, if_pos hyz]]
        rw [emul_none]
        rw [emul_some_some]
        by_cases h1 : op x y + z = 1
        · -- C1: 矛盾 (NoBadPair via bad_pair_when_y_z_eq_one)
          exfalso
          obtain ⟨_, hyz1⟩ := bad_pair_when_y_z_eq_one hxy hyz h1
          exact NoBadPair.no_root y z ⟨hyz, hyz1⟩
        · -- C2: op (op x y) z = x by op_op_eq_left
          rw [if_neg h1]
          congr 1
          exact op_op_eq_left_when_y_z_eq_one hxy hyz h1
      · -- ケース D (x+y≠1, y+z≠1)
        rw [show emul (some y) (some z) = some (op y z) from by
              rw [emul_some_some, if_neg hyz]]
        rw [emul_some_some, emul_some_some]
        by_cases h1 : op x y + z = 1
        · by_cases h2 : x + op y z = 1
          · -- D11: 両側 = none
            rw [if_pos h1, if_pos h2]
          · -- D12: 矛盾 (D=0 から両方とも =1 になるはず)
            exfalso
            have hD : D x y z = 0 := (op_add_eq_one_iff hxy z).mp h1
            exact h2 ((add_op_eq_one_iff hyz x).mpr hD)
        · by_cases h2 : x + op y z = 1
          · -- D21: 矛盾 (対称)
            exfalso
            have hD : D x y z = 0 := (add_op_eq_one_iff hyz x).mp h2
            exact h1 ((op_add_eq_one_iff hxy z).mpr hD)
          · -- D22: op_assoc を適用
            rw [if_neg h1, if_neg h2]
            congr 1
            exact op_assoc hxy hyz h1 h2

end OptionExt

/-! ## §7 Group インスタンス -/

noncomputable instance instGroup [NoBadPair F] : Group (Option F) where
  mul := OptionExt.emul
  one := none
  inv := OptionExt.einv
  mul_assoc := OptionExt.emul_assoc
  one_mul := OptionExt.none_emul
  mul_one := OptionExt.emul_none
  inv_mul_cancel := OptionExt.einv_emul_self

end ExtendedGroup

