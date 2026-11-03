import Langlands.GroupScheme.Dynamic.ActionConjugation
import Langlands.GroupScheme.AutomorphicAction.BaseChange

/-! # Restriction and conjugation compatibility of pulled-back actions -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

set_option backward.isDefEq.respectTransparency false

variable {B S : Scheme.{u}} (b : S ⟶ B)
    {H G : GroupScheme B} (a : AutomorphicAction H G)

/-- Pullback commutes with restricting the acting group. -/
theorem baseChange_restrict {K : GroupScheme B} (f : K ⟶ H) :
    (a.restrict f).baseChange b =
      (a.baseChange b).restrict ((GroupScheme.baseChange b).map f) := by
  apply ext_act
  intro V h g
  apply (baseChangePointsEquiv b G V).injective
  rw [baseChangePointsEquiv_act, restrict_act, restrict_act, baseChangePointsEquiv_act,
    baseChangePointsEquiv_comp]

/-- The pullback of ambient conjugation is ambient conjugation after pullback. -/
theorem baseChange_conjugation (i : H ⟶ G) :
    (conjugation i).baseChange b =
      conjugation ((GroupScheme.baseChange b).map i) := by
  apply ext_act
  intro V h g
  apply (baseChangePointsEquiv b G V).injective
  rw [baseChangePointsEquiv_act, conjugation_act, conjugation_act, map_mul, map_mul, map_inv,
    baseChangePointsEquiv_comp]

end Langlands.GroupScheme.AutomorphicAction
