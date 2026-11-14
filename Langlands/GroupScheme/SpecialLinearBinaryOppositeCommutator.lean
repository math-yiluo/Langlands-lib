import Langlands.GroupScheme.SpecialLinearDynamicRoots
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Monoid.WithTop

/-! # Explicit opposite-root commutator factors in SL₂ -/

noncomputable section

namespace Langlands.GroupScheme.SpecialLinear.BinaryRoot

universe u

variable {E : Type u} [Field E]

local notation "upper" =>
  Matrix.SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1)
local notation "lower" =>
  Matrix.SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0)
local notation "diagonal" =>
  Root.contractingMatrix (zero_ne_one : (0 : Fin 2) ≠ 1)

/-- The leading entry of an upper/lower root-matrix product. -/
def oppositeProductPivot (a b : E) : E := 1 + a * b

/-- A nonzero pivot gives actual lower/diagonal/upper factors. -/
theorem upper_mul_lower_factorization (a b : E) (h : oppositeProductPivot a b ≠ 0) :
    upper a * lower b =
      lower (b / oppositeProductPivot a b) *
        diagonal (Units.mk0 (oppositeProductPivot a b) h) *
          upper (a / oppositeProductPivot a b) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe, Root.contractingMatrix,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, Matrix.one_apply,
      Units.val_inv_eq_inv_val] <;>
    field_simp <;> simp_all [oppositeProductPivot]
  all_goals ring

/-- The KP commutator convention has the same pivot as the upper/lower product. -/
theorem oppositeCommutator_factorization (a b : E) (h : oppositeProductPivot a b ≠ 0) :
    (lower b)⁻¹ * upper a * lower b * (upper a)⁻¹ =
      lower (b / oppositeProductPivot a b - b) *
        diagonal (Units.mk0 (oppositeProductPivot a b) h) *
          upper (a / oppositeProductPivot a b - a) := by
  calc
    (lower b)⁻¹ * upper a * lower b * (upper a)⁻¹ =
        (lower b)⁻¹ * (upper a * lower b) * (upper a)⁻¹ := by
      simp only [mul_assoc]
    _ = _ := by
      rw [upper_mul_lower_factorization a b h]
      rw [show b / oppositeProductPivot a b - b = -b + b / oppositeProductPivot a b by ring]
      simp only [sub_eq_add_neg, Matrix.SpecialLinearGroup.transvection_add,
        Matrix.SpecialLinearGroup.transvection_inv]
      simp only [mul_assoc]

section Valuation

variable (omega : AddValuation E (WithTop ℝ))

/-- The pivot deviation has exactly the sum of the two root-coordinate values. -/
theorem value_oppositeProductPivot_sub_one (a b : E) :
    omega (oppositeProductPivot a b - 1) = omega a + omega b := by
  simp [oppositeProductPivot, omega.map_mul]

/-- A positive sum of root-coordinate values forces the pivot to be nonzero. -/
theorem oppositeProductPivot_ne_zero_of_value_sum (a b : E) (r : ℝ) (hr : 0 < r)
    (hvalue : omega a + omega b = (r : WithTop ℝ)) :
    oppositeProductPivot a b ≠ 0 := by
  have ht := value_oppositeProductPivot_sub_one omega a b
  rw [hvalue] at ht
  intro hzero
  rw [hzero, zero_sub, omega.map_neg, omega.map_one] at ht
  have he : (0 : ℝ) = r := WithTop.coe_injective ht
  linarith

/-- Positive opposite-root depth sum gives actual commutator factors and its
exact diagonal congruence value. -/
theorem exists_oppositeCommutator_factorization_of_value_sum
    (a b : E) (r : ℝ) (hr : 0 < r)
    (hvalue : omega a + omega b = (r : WithTop ℝ)) :
    ∃ (b' a' : E) (t : Eˣ),
      (lower b)⁻¹ * upper a * lower b * (upper a)⁻¹ =
        lower b' * diagonal t * upper a' ∧
      omega ((t : E) - 1) = (r : WithTop ℝ) := by
  let ht := oppositeProductPivot_ne_zero_of_value_sum omega a b r hr hvalue
  refine ⟨b / oppositeProductPivot a b - b, a / oppositeProductPivot a b - a,
    Units.mk0 (oppositeProductPivot a b) ht, oppositeCommutator_factorization a b ht, ?_⟩
  exact (value_oppositeProductPivot_sub_one omega a b).trans hvalue

end Valuation

end Langlands.GroupScheme.SpecialLinear.BinaryRoot
