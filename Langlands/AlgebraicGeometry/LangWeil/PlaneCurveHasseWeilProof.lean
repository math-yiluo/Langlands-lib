import Langlands.AlgebraicGeometry.LangWeil.PlaneCurveHasseWeilReduction
import Langlands.AlgebraicGeometry.LangWeil.PlaneCurveElementaryReductionsProof
import Langlands.AlgebraicGeometry.LangWeil.Stepanov.NormPolynomials

/-!
# Proof of Schmidt's Hasse–Weil bound for absolutely irreducible plane curves

Combines the conditional reduction `planeCurveHasseWeil_of_stepanov` with the proofs of its
two inputs: the Stepanov norm-polynomial construction (`Stepanov.stepanovNormPolynomials`)
and the elementary coordinate reductions (`planeCurveElementaryReductions`, Library).
-/

universe u

namespace Langlands.AlgebraicGeometry.LangWeil

/-- Schmidt's bound `|A - q| < 2 min(m² n, n² m) q^{1/2}` for an absolutely irreducible plane
curve over a finite field with `q > 9 (m + 1)² (n + 1)²`. -/
theorem planeCurveHasseWeil : PlaneCurveHasseWeilStatement.{u} :=
  planeCurveHasseWeil_of_stepanov Stepanov.stepanovNormPolynomials planeCurveElementaryReductions

end Langlands.AlgebraicGeometry.LangWeil
