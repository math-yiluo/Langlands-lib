import Langlands.CategoryTheory.RationalizationScaledActions

/-! # Positive denominators for exact scaled integral lifts -/

noncomputable section

open CategoryTheory

set_option autoImplicit false

universe v u w

namespace Langlands.Rationalization.ScaledIntegralLift

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {O : Type w} [Ring O] {X : C} {α : O →+* Rationalization.End X}

/-- Negating both the denominator and the integral linear lift preserves all exact laws. -/
def neg (s : ScaledIntegralLift α) : ScaledIntegralLift α where
  denom := -s.denom
  denom_ne_zero := neg_ne_zero.mpr s.denom_ne_zero
  map := -s.map
  ofEnd_map x := by
    simp only [LinearMap.neg_apply, map_neg, s.ofEnd_map, neg_zsmul]
  map_one := by
    simp only [LinearMap.neg_apply, s.map_one, neg_zsmul]
  map_mul x y := by
    simp only [LinearMap.neg_apply, neg_mul_neg, s.map_mul, neg_zsmul, smul_neg, neg_neg]

/-- Choose the sign of the lift so that its denominator is positive. -/
def positive (s : ScaledIntegralLift α) : ScaledIntegralLift α :=
  if 0 < s.denom then s else s.neg

/-- The normalized denominator is strictly positive. -/
theorem positive_denom_pos (s : ScaledIntegralLift α) : 0 < s.positive.denom := by
  by_cases h : 0 < s.denom
  · simpa only [positive, ite_eq_left h] using h
  · simp only [positive, ite_eq_right h, neg]
    exact neg_pos.mpr ((lt_or_gt_of_ne s.denom_ne_zero).resolve_right h)

/-- The normalized denominator as a natural torsion index. -/
def positiveIndex (s : ScaledIntegralLift α) : ℕ := s.positive.denom.natAbs

/-- The natural index casts back to the exact normalized denominator. -/
@[simp] theorem positiveIndex_cast (s : ScaledIntegralLift α) :
    (s.positiveIndex : ℤ) = s.positive.denom := by
  exact Int.natAbs_of_nonneg (le_of_lt s.positive_denom_pos)

/-- The natural torsion index is strictly positive. -/
theorem positiveIndex_pos (s : ScaledIntegralLift α) : 0 < s.positiveIndex := by
  have h := s.positive_denom_pos
  rw [← s.positiveIndex_cast] at h
  exact_mod_cast h

end Langlands.Rationalization.ScaledIntegralLift
