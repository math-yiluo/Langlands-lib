import Langlands.GroupScheme.Rational.CentralQuotientCenter
import Langlands.GroupScheme.Torus.CommutativeNoTorusBaseChange

/-! # Largest central subtori commute with arbitrary field extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- The largest central subtorus of a connected reductive field group remains
largest after every extension of the base field. -/
theorem reductiveLargestCentralSubtorusBaseChange :
    ReductiveLargestCentralSubtorusBaseChangeStatement.{u} := by
  intro k K _ _ _ G Z z hG hz
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : ConnectedSpace G.X.left := hG.connectedSpace
  obtain ⟨Q, q, hQs, hQa, hq⟩ :=
    normalSubgroupQuotient k G Z.toGrp z hz.isClosedSubgroup hz.isCentral.range_isNormal
  let : Smooth Q.X.hom := hQs
  let : IsAffineHom Q.X.hom := hQa
  obtain ⟨C, c, hc⟩ := schemeTheoreticCenterExistence_of_isAffineHom hQa
  let : IsClosedImmersion c.hom.hom.left := hc.1
  let : Mono c.hom.hom := hc.isRepresentedBy.1
  let Cc := hc.isCentral.commGroupScheme
  let : IsAffineHom C.X.hom := by
    rw [← Over.w c.hom.hom]
    infer_instance
  let : IsAffine C.X.left := isAffine_of_isAffineHom C.X.hom
  let : LocallyOfFiniteType C.X.hom := by
    rw [← Over.w c.hom.hom]
    infer_instance
  let : IsAffine Cc.toGrp.X.left := inferInstanceAs (IsAffine C.X.left)
  let : LocallyOfFiniteType Cc.toGrp.X.hom :=
    inferInstanceAs (LocallyOfFiniteType C.X.hom)
  have hC : ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))), IsTorus T.toGrp →
      ∀ f : T.toGrp ⟶ Cc.toGrp, SubgroupFunctor.range f = ⊥ := by
    intro T hT f
    rw [hz.quotient_center_torus_hom_eq_zero q hq hc T hT f,
      SubgroupFunctor.range_zero]
  apply hz.baseChange_of_quotient_center q hq hc
  intro T hT f
  exact CocharacterDatum.torus_hom_eq_zero_of_no_torus (Z := Cc) hC K T hT f

end Langlands.GroupScheme
