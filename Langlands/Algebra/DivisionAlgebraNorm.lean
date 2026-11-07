import Langlands.Algebra.DivisionNormValuation
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The degree-normalized determinant norm on a finite-dimensional division algebra. -/

noncomputable section

namespace Langlands.CentralDivision

universe u v

variable (K : Type u) (D : Type v) [NontriviallyNormedField K] [CompleteSpace K]
  [IsUltrametricDist K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]

omit [CompleteSpace K] [IsUltrametricDist K] in
private theorem finrank_real_pos : 0 < (Module.finrank K D : ℝ) :=
  Nat.cast_pos.mpr (Module.finrank_pos (R := K) (M := D))

/-- The positive degree root of the absolute value of the regular determinant norm. -/
def regularAbsoluteValue : AbsoluteValue D ℝ where
  toFun x := (regularNormValuation K D x : ℝ) ^ (Module.finrank K D : ℝ)⁻¹
  map_mul' x y := by
    simp only [map_mul, NNReal.coe_mul]
    exact Real.mul_rpow (by positivity) (by positivity)
  nonneg' x := Real.rpow_nonneg (by positivity) _
  eq_zero' x := by
    rw [Real.rpow_eq_zero (by positivity) (inv_ne_zero (finrank_real_pos K D).ne')]
    exact_mod_cast (regularNormValuation K D).zero_iff
  add_le' x y := by
    have h : (regularNormValuation K D (x + y) : ℝ) ≤
        max (regularNormValuation K D x : ℝ) (regularNormValuation K D y : ℝ) := by
      exact_mod_cast (regularNormValuation K D).map_add x y
    calc
      _ ≤ (max (regularNormValuation K D x : ℝ)
          (regularNormValuation K D y : ℝ)) ^ (Module.finrank K D : ℝ)⁻¹ :=
        Real.rpow_le_rpow (by positivity) h (by positivity)
      _ = max ((regularNormValuation K D x : ℝ) ^ (Module.finrank K D : ℝ)⁻¹)
          ((regularNormValuation K D y : ℝ) ^ (Module.finrank K D : ℝ)⁻¹) :=
        Real.rpow_max (by positivity) (by positivity) (by positivity)
      _ ≤ _ := max_le_add_of_nonneg (by positivity) (by positivity)

@[simp]
theorem regularAbsoluteValue_apply (x : D) :
    regularAbsoluteValue K D x =
      ‖Algebra.norm K x‖ ^ (Module.finrank K D : ℝ)⁻¹ := rfl

/-- The normalization makes the absolute value restrict to the given base norm. -/
@[simp]
theorem regularAbsoluteValue_algebraMap (a : K) :
    regularAbsoluteValue K D (algebraMap K D a) = ‖a‖ := by
  change (regularNormValuation K D (algebraMap K D a) : ℝ) ^
    (Module.finrank K D : ℝ)⁻¹ = _
  rw [regularNormValuation_algebraMap, NNReal.coe_pow, coe_nnnorm]
  exact Real.pow_rpow_inv_natCast (norm_nonneg _) (Module.finrank_pos.ne')

/-- The normalized determinant norm is still nonarchimedean. -/
theorem regularAbsoluteValue_add_le (x y : D) :
    regularAbsoluteValue K D (x + y) ≤
      max (regularAbsoluteValue K D x) (regularAbsoluteValue K D y) := by
  change (regularNormValuation K D (x + y) : ℝ) ^ (Module.finrank K D : ℝ)⁻¹ ≤
    max ((regularNormValuation K D x : ℝ) ^ (Module.finrank K D : ℝ)⁻¹)
      ((regularNormValuation K D y : ℝ) ^ (Module.finrank K D : ℝ)⁻¹)
  rw [← Real.rpow_max (by positivity) (by positivity) (by positivity)]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  exact_mod_cast (regularNormValuation K D).map_add x y

/-- Raising to the dimension recovers the original regular determinant absolute value. -/
theorem regularAbsoluteValue_pow_finrank (x : D) :
    regularAbsoluteValue K D x ^ Module.finrank K D = ‖Algebra.norm K x‖ :=
  Real.rpow_inv_natCast_pow (norm_nonneg _) (Module.finrank_pos.ne')

/-- Normalization preserves and reflects comparisons of regular determinant absolute values. -/
theorem regularAbsoluteValue_le_iff (x y : D) :
    regularAbsoluteValue K D x ≤ regularAbsoluteValue K D y ↔
      ‖Algebra.norm K x‖ ≤ ‖Algebra.norm K y‖ :=
  Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _)
    (inv_pos.mpr (finrank_real_pos K D))

/-- Normalization preserves and reflects strict comparisons as well. -/
theorem regularAbsoluteValue_lt_iff (x y : D) :
    regularAbsoluteValue K D x < regularAbsoluteValue K D y ↔
      ‖Algebra.norm K x‖ < ‖Algebra.norm K y‖ :=
  Real.rpow_lt_rpow_iff (norm_nonneg _) (norm_nonneg _)
    (inv_pos.mpr (finrank_real_pos K D))

/-- The normed-ring structure constructed from the normalized determinant norm. -/
@[instance_reducible]
def regularNormedRing : NormedRing D := (regularAbsoluteValue K D).toNormedRing

/-- The constructed norm makes the original central scalar action a normed algebra action. -/
@[instance_reducible]
def regularNormedAlgebra :
    letI := regularNormedRing K D
    NormedAlgebra K D := by
  letI := regularNormedRing K D
  refine { ‹Algebra K D› with norm_smul_le := ?_ }
  intro a x
  change regularAbsoluteValue K D (a • x) ≤ ‖a‖ * regularAbsoluteValue K D x
  rw [Algebra.smul_def, map_mul, regularAbsoluteValue_algebraMap]

end Langlands.CentralDivision
