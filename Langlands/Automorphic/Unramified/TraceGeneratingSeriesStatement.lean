import Langlands.Automorphic.Unramified.TraceGeneratingSeries
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
Internal derived prerequisite statements for the published trace-algebra
targets. These closed proposition definitions supply no proofs or automorphic
assumptions. The imported formal-series helper is unchanged.
-/

open scoped BigOperators

namespace Langlands.Automorphic.Unramified

/-- Every positive coefficient of the normalized characteristic-polynomial
trace series is the corresponding matrix power trace, including zero rank
and arbitrary singular or nonsemisimple complex matrices. -/
def MatrixTraceGeneratingSeriesStatement : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ), 0 < k →
    PowerSeries.coeff k (polynomialTraceSeries A.charpolyRev) =
      Matrix.trace (A ^ k)

/-- On complex polynomials with constant term one, equality of trace series
is equivalent to polynomial equality, and finite products give sums of series.
Empty families are included. -/
def PolynomialTraceGeneratingSeriesStatement : Prop :=
  (∀ (P Q : Polynomial ℂ), P.coeff 0 = 1 → Q.coeff 0 = 1 →
    (polynomialTraceSeries P = polynomialTraceSeries Q ↔ P = Q)) ∧
  (∀ (a : ℕ) (P : Fin a → Polynomial ℂ), (∀ i, (P i).coeff 0 = 1) →
    polynomialTraceSeries (∏ i, P i) = ∑ i, polynomialTraceSeries (P i))

end Langlands.Automorphic.Unramified
