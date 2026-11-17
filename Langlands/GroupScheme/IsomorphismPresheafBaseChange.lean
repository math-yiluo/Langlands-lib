import Langlands.GroupScheme.IsomorphismPresheaf
import Langlands.GroupScheme.IsomorphismSchemeBaseChange

/-! # Pulling back a representation of the full Isom presheaf -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.GroupScheme.LocalGroupIso

variable {S S' : Scheme.{u}} (b : S' ⟶ S) {G H : GroupScheme S}

/-- A supplied representation pulls back to a representation by the actual
pullback of its parameter scheme. -/
def representableByBaseChange {P : Over S}
    (R : (presheaf G H).RepresentableBy P) :
    (presheaf ((baseChange b).obj G) ((baseChange b).obj H)).RepresentableBy
      ((Over.pullback b).obj P) :=
  ((GroupIsomorphismScheme.ofRepresentableBy R).baseChange b).representableBy

/-- The new classification map is the old classification map followed by
the all-test base-change equivalence. -/
theorem representableByBaseChange_homEquiv {P : Over S}
    (R : (presheaf G H).RepresentableBy P) {T : Over S'}
    (p : T ⟶ (Over.pullback b).obj P) :
    (representableByBaseChange b R).homEquiv p =
      (R.homEquiv (((Over.mapPullbackAdj b).homEquiv T P).symm p)).baseChangeFamily b := by
  change ((GroupIsomorphismScheme.ofRepresentableBy R).baseChangeUniversalIso b).refine p = _
  refine ((GroupIsomorphismScheme.ofRepresentableBy R).baseChangeUniversalIso_refine b p).trans ?_
  change ((R.homEquiv (𝟙 P)).refine
    (((Over.mapPullbackAdj b).homEquiv T P).symm p)).baseChangeFamily b = _
  exact congrArg (fun e : LocalGroupIso G H ((Over.map b).obj T) => e.baseChangeFamily b)
    (R.homEquiv_eq (((Over.mapPullbackAdj b).homEquiv T P).symm p)).symm

end Langlands.GroupScheme.LocalGroupIso
