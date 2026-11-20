import Langlands.Representation.RankinSelberg.NormalizedZetaEvaluation
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Finite combinations of normalized rational zeta values -/

noncomputable section

set_option autoImplicit false

open Polynomial Set

namespace Langlands.RankinSelberg

variable {values : Set RationalFunctions} {P : ℂ[X]} (h : IsNormalizedGenerator values P)

private theorem exists_reciprocalCombination (h : IsNormalizedGenerator values P) :
    ∃ c : values →₀ LaurentCoefficients,
      ∑ R ∈ c.support, c R • (R : RationalFunctions) = (algebraMap ℂ[X] RationalFunctions P)⁻¹ := by
  have hinv := (isNormalizedGenerator_iff values P).mp h |>.2.2
  obtain ⟨c, hc⟩ :=
    (Finsupp.mem_span_iff_linearCombination LaurentCoefficients values _).mp hinv
  refine ⟨c, ?_⟩
  simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using hc

/-- A Laurent combination of rational zeta values giving the reciprocal of the L-polynomial. -/
def IsNormalizedGenerator.reciprocalCombination : values →₀ LaurentCoefficients :=
  (exists_reciprocalCombination h).choose

/-- The normalized Laurent values span the unit by the same finite combination. -/
theorem IsNormalizedGenerator.reciprocalCombination_spec :
    ∑ R ∈ h.reciprocalCombination.support,
      h.reciprocalCombination R * h.normalizedLaurent ⟨R, mem_zetaSpan R.property⟩ = 1 := by
  let c := h.reciprocalCombination
  have hc := (exists_reciprocalCombination h).choose_spec
  apply laurentToRatFunc_injective
  rw [map_sum, map_one]
  calc
    _ = ∑ R ∈ c.support,
        algebraMap ℂ[X] RationalFunctions P * (c R • (R : RationalFunctions)) := by
      apply Finset.sum_congr rfl
      intro R _
      rw [map_mul, h.normalizedLaurent_spec, Algebra.smul_def, algebraMap_laurent]
      ring
    _ = algebraMap ℂ[X] RationalFunctions P * ∑ R ∈ c.support, c R • (R : RationalFunctions) :=
      (Finset.mul_sum ..).symm
    _ = 1 := by
      change ∑ R ∈ c.support, c R • (R : RationalFunctions) = _ at hc
      rw [hc, mul_inv_cancel₀ (RatFunc.algebraMap_ne_zero h.polynomial_ne_zero)]

/-- At any nonzero point, the same weighted sum of normalized values is one. -/
theorem IsNormalizedGenerator.reciprocalCombination_eval (z : ℂˣ) :
    ∑ R ∈ h.reciprocalCombination.support,
      laurentEval z (h.reciprocalCombination R) *
        laurentEval z (h.normalizedLaurent ⟨R, mem_zetaSpan R.property⟩) = 1 := by
  simpa only [map_sum, map_mul, map_one] using
    congrArg (laurentEval z) h.reciprocalCombination_spec

/-- Laurent evaluation at the local spectral parameter is bounded on every closed strip. -/
theorem exists_bound_laurentEval_spectralUnit {q : ℕ} (hq : 1 < q)
    (a : LaurentCoefficients) (l r : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, l ≤ s.re → s.re ≤ r →
      ‖laurentEval (spectralUnit (Nat.zero_lt_one.trans hq) s) a‖ ≤ C := by
  induction a using LaurentPolynomial.induction_on_mul_T with
  | mul_T p n =>
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq.le
    have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_one.trans hq
    let outer := (q : ℝ) ^ (-l)
    let inner := (q : ℝ) ^ (-r)
    let A : Set ℂ := Metric.closedBall 0 outer ∩ {z | inner ≤ ‖z‖}
    have hA : IsCompact A :=
      (isCompact_closedBall 0 outer).inter_right (isClosed_le continuous_const continuous_norm)
    have hne (z : ℂ) (hz : z ∈ A) : z ≠ 0 :=
      norm_pos_iff.mp ((Real.rpow_pos_of_pos hq0 _).trans_le hz.2)
    have hcont : ContinuousOn (fun z : ℂ => p.eval z * z ^ (-(n : ℤ))) A :=
      p.continuous.continuousOn.mul (continuous_id.continuousOn.zpow₀ _ (fun z hz => Or.inl (hne z hz)))
    obtain ⟨C, hC⟩ := hA.exists_bound_of_continuousOn hcont
    refine ⟨C, fun s hl hr => ?_⟩
    simp only [map_mul, laurentEval_toLaurent, laurentEval_T, coe_spectralUnit]
    apply hC
    simp only [A, mem_inter_iff, Metric.mem_closedBall, dist_zero_right, mem_ofPred_eq,
      spectralPoint, Complex.norm_natCast_cpow_of_pos (Nat.zero_lt_one.trans hq), Complex.neg_re]
    exact ⟨Real.rpow_le_rpow_of_exponent_le hqR (neg_le_neg hl),
      Real.rpow_le_rpow_of_exponent_le hqR (neg_le_neg hr)⟩

end Langlands.RankinSelberg
