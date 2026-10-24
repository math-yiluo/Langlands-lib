import Langlands.Representation.RankinSelberg.NormalizedGeneratorRegularityStatement

noncomputable section

namespace Langlands.RankinSelberg

open Polynomial RationalEvaluation

/-- Laurent coefficients have no poles away from zero. -/
theorem regularAt_laurentToRatFunc (a : LaurentCoefficients) {z : ℂ}
    (hz : z ≠ 0) : RegularAt (laurentToRatFunc a) z := by
  induction a using LaurentPolynomial.induction_on_mul_T with
  | mul_T P n =>
    rw [map_mul, laurentToRatFunc_toLaurent, laurentToRatFunc_T]
    exact (RegularAt.polynomial P).mul
      (RegularAt.zpow (R := RatFunc.X) (by simpa using hz) _)

/-- Regularity away from zero passes from a set to its Laurent span. -/
theorem regularAt_of_mem_zetaSpan {values : Set RationalFunctions} {z : ℂ}
    (hz : z ≠ 0) (hvalues : ∀ R ∈ values, RegularAt R z)
    {R : RationalFunctions} (hR : R ∈ zetaSpan values) : RegularAt R z := by
  induction hR using Submodule.span_induction with
  | mem R hR => exact hvalues R hR
  | zero => simpa using (RegularAt.polynomial (z := z) (0 : ℂ[X]))
  | add R S _ _ hR hS => exact hR.add hS
  | smul a R _ hR =>
    simpa only [Algebra.smul_def, algebraMap_laurent] using
      (regularAt_laurentToRatFunc a hz).mul hR

/-- Regularity of the generating values excludes a root of the normalized
polynomial at every nonzero point. -/
theorem IsNormalizedGenerator.eval_ne_zero_of_regularAt
    {values : Set RationalFunctions} {P : ℂ[X]}
    (hP : IsNormalizedGenerator values P) {z : ℂ} (hz : z ≠ 0)
    (hvalues : ∀ R ∈ values, RegularAt R z) : P.eval z ≠ 0 := by
  have hmem : (algebraMap ℂ[X] RationalFunctions P)⁻¹ ∈ zetaSpan values := by
    rw [hP.2]
    exact Submodule.mem_span_singleton_self _
  have hinv := regularAt_of_mem_zetaSpan hz hvalues hmem
  have heval := RationalEvaluation.eval_mul
    (RegularAt.polynomial (z := z) P) hinv
  rw [mul_inv_cancel₀ (RatFunc.algebraMap_ne_zero hP.polynomial_ne_zero),
    RatFunc.eval_one] at heval
  intro hzero
  simp [hzero] at heval

/-- The normalization itself excludes a root at zero. -/
theorem IsNormalizedGenerator.eval_zero_ne_zero
    {values : Set RationalFunctions} {P : ℂ[X]}
    (hP : IsNormalizedGenerator values P) : P.eval 0 ≠ 0 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, hP.1]
  exact one_ne_zero

/-- Algebraic regularity of a normalized reciprocal generator. -/
theorem normalizedGeneratorRegularity : NormalizedGeneratorRegularityStatement := by
  intro values P hP z hz hvalues
  exact hP.eval_ne_zero_of_regularAt hz hvalues

end Langlands.RankinSelberg
