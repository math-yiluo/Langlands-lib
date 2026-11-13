import Langlands.AlgebraicGeometry.LangWeil.PlaneCurveHasseWeilProof
import Langlands.AlgebraicGeometry.LangWeil.FamilyLangWeilOfPlaneCurveProof
import Langlands.AlgebraicGeometry.LangWeil.SpaceUniformLangWeilOfFamilyProof
import Langlands.AlgebraicGeometry.LangWeil.FamilyPointUpperBoundProof

/-!
# Conrad's Lemma 4.6 for algebraic spaces

The algebraic-space form of Conrad's Lemma 4.6 (`SpaceUniformLangWeilStatement`) by the
elementary Lang–Weil route. Schmidt's plane-curve bound (`LangWeil.planeCurveHasseWeil`) gives
the uniform family estimate in every fibre dimension (`LangWeil.familyLangWeilOfPlaneCurve`).
With the uniform point upper bound (`LangWeil.familyPointUpperBound`), the reduction from
algebraic spaces with étale charts to scheme families (`LangWeil.spaceUniformLangWeilOfFamily`)
gives the statement.
-/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- **Conrad's Lemma 4.6 for algebraic spaces** (Conrad 2011, used in the proof of Theorem 5.9,
printed p.17), proved by the elementary Lang–Weil route. -/
theorem spaceUniformLangWeil : SpaceUniformLangWeilStatement.{u} :=
  LangWeil.spaceUniformLangWeilOfFamily
    (LangWeil.familyLangWeilOfPlaneCurve LangWeil.planeCurveHasseWeil)
    LangWeil.familyPointUpperBound

end Langlands.AlgebraicGeometry.AlgebraicSpace
