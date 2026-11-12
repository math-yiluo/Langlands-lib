import Langlands.AlgebraicGeometry.LangWeil.FamilyLangWeilStatement
import Langlands.AlgebraicGeometry.LangWeil.FamilyPointUpperBoundStatement
import Langlands.AlgebraicGeometry.LangWeil.PlaneCurveHasseWeilStatement

/-!
# The uniform Lang–Weil estimate for families of curves, from the plane-curve bound

The case `d = 1` of `FamilyLangWeilInDimension`, reduced to Schmidt's Hasse–Weil bound for
absolutely irreducible plane curves and the uniform upper bound for point counts in families.
-/

universe u

namespace Langlands.AlgebraicGeometry.LangWeil

/-- The Hasse–Weil bound for absolutely irreducible plane curves (`PlaneCurveHasseWeilStatement`)
and the uniform point-count upper bound in families (`FamilyPointUpperBoundStatement`) imply the
uniform Lang–Weil estimate in fibre dimension `1`. -/
def FamilyLangWeilCurveStatement : Prop :=
  PlaneCurveHasseWeilStatement.{u} → FamilyPointUpperBoundStatement.{u} →
    FamilyLangWeilInDimension.{u} 1

end Langlands.AlgebraicGeometry.LangWeil
