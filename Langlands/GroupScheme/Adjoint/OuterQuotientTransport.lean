import Langlands.GroupScheme.OuterIsomorphismTransport
import Langlands.GroupScheme.Adjoint.RelativeQuotientEquivariance
import Langlands.GroupScheme.Adjoint.RelativeQuotient
import Langlands.GroupScheme.AutomorphicAction.FppfCenterQuotient

/-! # Outer-quotient transport between supplied full-centre quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace IsRelativeAdjointQuotient

variable {S : Scheme.{u}} {G A B : GroupScheme S}
  {q : G ⟶ A} {p : G ⟶ B}
  (hq : IsRelativeAdjointQuotient q) (hp : IsRelativeAdjointQuotient p)

/-- The canonical comparison between two supplied full-centre quotients of one group. -/
def quotientIso : A ≅ B :=
  hq.isQuotient.mapIso hp.isQuotient (Iso.refl G)

/-- The canonical quotient comparison respects the supplied quotient maps. -/
theorem comp_quotientIso_hom : q ≫ (hq.quotientIso hp).hom = p := by
  simpa only [quotientIso, Iso.refl_hom, Category.id_comp] using
    hq.isQuotient.comp_mapIso_hom hp.isQuotient (Iso.refl G)

/-- The canonical full-centre quotient comparison identifies the inner actions
on every test, by locally lifting the acting point along the fppf quotient. -/
theorem innerAction_quotientIso {T : Over S} (d : T ⟶ A.X) (g : T ⟶ G.X) :
    hq.innerAction.act d g =
      hp.innerAction.act (d ≫ (hq.quotientIso hp).hom.hom.hom) g := by
  let : Flat q.hom.hom.left := hq.isQuotient.1
  let : Surjective q.hom.hom.left := hq.isQuotient.2.1
  let : LocallyOfFinitePresentation q.hom.hom.left := hq.isQuotient.2.2.1
  have hs : q.hom.hom ≫ (hq.quotientIso hp).hom.hom.hom = p.hom.hom :=
    congrArg (fun f => f.hom.hom) (hq.comp_quotientIso_hom hp)
  apply AutomorphicAction.hom_ext_of_fppf_local_quotient_lift q d
  intro V t x hx
  rw [hq.innerAction.naturality, hp.innerAction.naturality,
    ← Category.assoc, hx, Category.assoc, hs,
    AutomorphicAction.act_lift_of_restrict_eq_conjugation
      hq.innerAction hq.innerAction_restrict,
    AutomorphicAction.act_lift_of_restrict_eq_conjugation
      hp.innerAction hp.innerAction_restrict]

end IsRelativeAdjointQuotient

namespace OuterIsomorphismScheme

variable {S : Scheme.{u}} {G H A B : GroupScheme S}
  {q : G ⟶ A} {p : G ⟶ B}
  {hq : IsRelativeAdjointQuotient q} {hp : IsRelativeAdjointQuotient p}
  {I : GroupIsomorphismScheme G H}

/-- An outer quotient for one supplied adjoint quotient is also an outer quotient
for any other supplied adjoint quotient of the same group. -/
def changeAdjointQuotient (O : OuterIsomorphismScheme I hq.innerAction)
    (hp : IsRelativeAdjointQuotient p) : OuterIsomorphismScheme I hp.innerAction :=
  O.changeActingGroup hp.innerAction (hp.quotientIso hq)
    (fun _ d g => hp.innerAction_quotientIso hq d g)

end OuterIsomorphismScheme

end Langlands.GroupScheme
