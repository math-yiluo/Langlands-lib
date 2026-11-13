import Langlands.Global.AdelicSpaceSmoothConnectedSpreadOpen
import Langlands.AlgebraicGeometry.LangWeil.SpaceUniformLangWeilOfFamilyProof
import Langlands.AlgebraicGeometry.LangWeil.FamilyLangWeilOfPlaneCurveProof
import Langlands.AlgebraicGeometry.LangWeil.FamilyPointUpperBoundProof
import Langlands.AlgebraicGeometry.LangWeil.PlaneCurveHasseWeilProof

/-!
# Proof of Conrad's Theorem 5.9 for separated algebraic spaces

Conrad's Theorem 5.9 (`AdelicSpaceSpreadSmoothOpenStatement`) follows from the
algebraic-space form of his Lemma 4.6 (`SpaceUniformLangWeilStatement`) by the published
reduction `adelicSpaceSpreadSmoothOpen_of_langWeil`. That Lemma 4.6 input is assembled here
from published proofs only:

* Schmidt's Hasse–Weil bound for plane curves (`planeCurveHasseWeil`);
* the dimension induction giving the uniform family Lang–Weil estimate from it
  (`familyLangWeilOfPlaneCurve`);
* the uniform point-count upper bound in families (`familyPointUpperBound`);
* the stratification of algebraic spaces by scheme families (`spaceUniformLangWeilOfFamily`).
-/

universe u

namespace Langlands.Global

open Langlands.AlgebraicGeometry.LangWeil

/-- Conrad's Theorem 5.9 for global fields of both characteristics: a smooth surjective map
with geometrically connected fibres between algebraic spaces over a global field induces an
open map on adelic points, for arbitrary separated models of finite type over rings of
`S`-integers and the topologies they define. -/
theorem adelicSpaceSpreadSmoothOpen : AdelicSpaceSpreadSmoothOpenStatement.{u} :=
  adelicSpaceSpreadSmoothOpen_of_langWeil
    (spaceUniformLangWeilOfFamily (familyLangWeilOfPlaneCurve planeCurveHasseWeil)
      familyPointUpperBound)

end Langlands.Global
