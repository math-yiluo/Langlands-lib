import Langlands.AlgebraicGeometry.LangWeil.FamilyLangWeilStatement
import Langlands.AlgebraicGeometry.LangWeil.PlaneCurveHasseWeilStatement

/-!
# Uniform family Lang–Weil from the plane-curve estimate

This derived implication packages the dimension induction using the zero-dimensional
case, the curve reduction and the hyperplane-slicing step. Its sole hypothesis is the
plane-curve estimate; the point-count upper bound and generic Bertini theorem are
already proved in the Library.
-/

universe u

namespace Langlands.AlgebraicGeometry.LangWeil

/-- The plane-curve Hasse–Weil estimate implies the uniform Lang–Weil estimate for
geometrically irreducible scheme families over the integers in every fibre dimension. -/
def FamilyLangWeilOfPlaneCurveStatement : Prop :=
  PlaneCurveHasseWeilStatement.{u} → FamilyLangWeilStatement.{u}

end Langlands.AlgebraicGeometry.LangWeil
