import Langlands.AlgebraicGeometry.LangWeil.PlaneCurveHasseWeilProof
import Langlands.AlgebraicGeometry.LangWeil.FamilyLangWeilOfPlaneCurveProof
import Langlands.AlgebraicGeometry.LangWeil.UniformLangWeilOfFamilyProof

/-!
# Proof of Conrad's Lemma 4.6 for schemes

Conrad's Lemma 4.6 (`UniformLangWeilStatement`) by the elementary Lang–Weil route: Schmidt's
plane-curve bound (`LangWeil.planeCurveHasseWeil`) gives the uniform family estimate through the
dimension induction (`LangWeil.familyLangWeilOfPlaneCurve`), and the family estimate gives
Conrad's lemma (`LangWeil.uniformLangWeilOfFamily`).
-/

universe u

namespace Langlands.AlgebraicGeometry

/-- Conrad's Lemma 4.6 (printed p.12): for a smooth, separated, surjective, quasi-compact map
`f : Y ⟶ B` locally of finite type, with `B` of finite type over `ℤ`, whose fibres are
geometrically connected of pure dimension `d`, there is `C > 0` with
`|N_b - q_b ^ d| ≤ C q_b ^ (d - 1/2)` at every closed point `b` of `B`. -/
theorem uniformLangWeil : UniformLangWeilStatement.{u} :=
  LangWeil.uniformLangWeilOfFamily
    (LangWeil.familyLangWeilOfPlaneCurve LangWeil.planeCurveHasseWeil)

end Langlands.AlgebraicGeometry
