import Langlands.Automorphic.Unramified.TraceAlgebraStatement
import Langlands.Automorphic.Unramified.PolynomialTraceGeneratingSeriesProof
import Langlands.Automorphic.Unramified.MatrixTraceGeneratingSeriesProof

open scoped BigOperators
open Polynomial

namespace Langlands.Automorphic.Unramified

/-- The complete determinant-product and positive-power-trace equivalence. -/
theorem eulerProductTrace : EulerProductTraceStatement := by
  classical
  have family_coeff : ∀ (a : ℕ) (n : Fin a → ℕ)
      (A : (i : Fin a) → Matrix (Fin (n i)) (Fin (n i)) ℂ) (k : ℕ), 0 < k →
      PowerSeries.coeff k (polynomialTraceSeries (∏ i, (A i).charpolyRev)) =
        ∑ i, Matrix.trace ((A i) ^ k) := by
    intro a n A k hk
    rw [polynomialTraceSeries_prod Finset.univ (fun i => (A i).charpolyRev)
      (fun i _ => by simp [Polynomial.coeff_zero_eq_eval_zero]), map_sum]
    exact Finset.sum_congr rfl fun i _ => matrixTraceGeneratingSeries (n i) (A i) k hk
  intro a b n m A B
  have hA0 : (∏ i, (A i).charpolyRev).coeff 0 = 1 := by
    simp [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
  have hB0 : (∏ j, (B j).charpolyRev).coeff 0 = 1 := by
    simp [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
  constructor
  · intro h k hk
    have hc := congrArg (PowerSeries.coeff k) (congrArg polynomialTraceSeries h)
    rw [family_coeff a n A k hk, family_coeff b m B k hk] at hc
    exact hc
  · intro h
    apply (polynomialTraceSeries_injective_normalized _ _ hA0 hB0).mp
    apply PowerSeries.ext
    intro k
    cases k with
    | zero => simp
    | succ k =>
      rw [family_coeff a n A (k + 1) (Nat.succ_pos k),
        family_coeff b m B (k + 1) (Nat.succ_pos k)]
      exact h (k + 1) (Nat.succ_pos k)

end Langlands.Automorphic.Unramified
