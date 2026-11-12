import Langlands.AlgebraicGeometry.LangWeil.FamilyLangWeilCurvePlaneReduction
import Langlands.AlgebraicGeometry.LangWeil.FamilyCurvePlaneComparisonProof

/-!
# The uniform Lang–Weil estimate for curve families

The bounded plane-model comparison and the arithmetic reduction prove the
published curve-family implication.
-/

universe u

namespace Langlands.AlgebraicGeometry.LangWeil

/-- The plane-curve bound and the uniform family upper bound imply the uniform
Lang–Weil estimate for geometrically irreducible curve families. -/
theorem familyLangWeilCurve : FamilyLangWeilCurveStatement.{u} :=
  familyLangWeilCurve_of_planeComparison familyCurvePlaneComparison

end Langlands.AlgebraicGeometry.LangWeil
