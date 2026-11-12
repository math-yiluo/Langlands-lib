import Langlands.AlgebraicGeometry.LangWeil.AffineCurvePlaneComparison
import Langlands.AlgebraicGeometry.LangWeil.FamilyCurvePlaneReduction

/-!
# Proof of the plane-model comparison for curve families

The affine core `CurvePlane.affineCurvePlaneComparison` and the reduction
`CurvePlane.familyCurvePlaneComparison_of_core` prove
`FamilyCurvePlaneComparisonStatement`.
-/

universe u

namespace Langlands.AlgebraicGeometry.LangWeil

/-- A family of geometrically irreducible curves admits uniform plane-curve comparisons over
sufficiently large finite fields. -/
theorem familyCurvePlaneComparison : FamilyCurvePlaneComparisonStatement.{u} :=
  CurvePlane.familyCurvePlaneComparison_of_core CurvePlane.affineCurvePlaneComparison

end Langlands.AlgebraicGeometry.LangWeil
