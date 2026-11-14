import Langlands.BruhatTits.IntegralModels.ReductiveQuotientRoots
import Langlands.GroupScheme.IntegralModel.UnipotentQuotientCell
import Langlands.GroupScheme.IntegralModel.ConnectedFibreDescent
import Langlands.GroupScheme.IntegralModel.GenericOppositeCell
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Rational.SplitUnipotentTransport

/-! # Generic opposite-cell factors from a quotient reduction -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.BruhatTits.IntegralModels

namespace SpecialFibreQuotientData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {D : RelativeComponentModelData R K G}
    (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient)

include hQ in
/-- A quotient reduction in the opposite dynamic unipotent gives actual
generic opposite-cell factors of the original integral section. -/
theorem generic_oppositeCell_of_quotient_unipotent
    (χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ D.neutral.group)
    (x : D.neutral.integralSections)
    (hx : rationalPoints.map Q.projection (D.neutral.reduction x) ∈
      (Dynamic.unipotent (Dynamic.oppositeCocharacter
        (Dynamic.baseChangeCocharacter (IntegralModel.residueBaseMap R) χ ≫
          Q.projection))).carrier (Over.mk (𝟙 _))) :
    ∃ v ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter
        (Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ ≫
          D.neutral.genericIso.hom))).carrier (Over.mk (𝟙 _)),
      ∃ w ∈ (Dynamic.parabolic
        (Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ ≫
          D.neutral.genericIso.hom)).carrier (Over.mk (𝟙 _)),
        D.neutral.integralPointMap x = v * w := by
  let : Smooth D.neutral.group.X.hom := D.neutral_smooth
  let : ConnectedSpace D.neutral.specialFibre.X.left :=
    D.neutral.hasConnectedSpecialFibre_of_hasConnectedFibres D.neutral_connectedFibres
  let : IsAffine D.neutral.group.X.left :=
    isAffine_of_isAffineHom D.neutral.group.X.hom
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  let : ConnectedSpace Q.quotient.X.left := hQ.2.2.connectedSpace
  let : IsAffine Q.quotient.X.left := isAffine_of_isAffineHom Q.quotient.X.hom
  let : IsClosedImmersion Q.radicalInclusion.hom.hom.left := hQ.1.isClosedSubgroup
  let : Mono Q.radicalInclusion.hom.hom := Over.mono_of_mono_left _
  let e := hQ.2.1.kernelIso (z := Q.radicalInclusion) ⟨inferInstance, rfl⟩
  let es := (Over.forget _).mapIso ((Grp.forget _).mapIso e)
  let : ConnectedSpace (kernel Q.projection).X.left :=
    es.inv.homeomorph.connectedSpace_iff.mpr hQ.1.connectedSpace
  have hN : IsUnipotent (kernel Q.projection) :=
    IsUnipotent.of_iso e.symm hQ.1.isUnipotent
  let χQ := Dynamic.baseChangeCocharacter (IntegralModel.residueBaseMap R) χ ≫
    Q.projection
  let j := Dynamic.Affine.unipotentHom (Dynamic.oppositeCocharacter χQ)
  let r := Dynamic.Affine.parabolicHom χQ
  have hj := Dynamic.Affine.isRepresentedBy_unipotentHom (Dynamic.oppositeCocharacter χQ)
  have hr := Dynamic.Affine.isRepresentedBy_parabolicHom χQ
  have hx' : rationalPoints.map Q.projection (D.neutral.reduction x) ∈
      (SubgroupFunctor.range j).carrier (Over.mk (𝟙 _)) := by
    rw [hj.2]
    exact hx
  obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp hx'
  let b := lift v (1 : Over.mk (𝟙 _) ⟶ (Dynamic.Affine.parabolicScheme χQ).X)
  have hb : b ≫ SubgroupFunctor.cellMultiplication j r =
      D.neutral.reduction x ≫ Q.projection.hom.hom := by
    simp only [b, SubgroupFunctor.lift_cellMultiplication, MonObj.one_comp, mul_one]
    exact hv
  let i := Dynamic.Affine.unipotentHom (Dynamic.oppositeCocharacter χ)
  let p := Dynamic.Affine.parabolicHom χ
  have hi := Dynamic.Affine.isRepresentedBy_unipotentHom (Dynamic.oppositeCocharacter χ)
  have hp := Dynamic.Affine.isRepresentedBy_parabolicHom χ
  obtain ⟨a, ha⟩ := (D.neutral.oppositeCell_section_lifts_iff_quotient_reduction
    χ i p hi hp Q.projection (Q.projection_smooth hQ) hQ.2.1.2.1 hN j r hj hr x).mpr ⟨b, hb⟩
  exact D.neutral.generic_oppositeCell_of_integral_lift χ i p hi hp x a ha


/-- A selected generic opposite-cell factor pair with the memberships and
exact product equality retained, obtained from the quotient reduction. -/
def genericOppositeCellFactorPairOfQuotientUnipotent
    (χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ D.neutral.group)
    (x : D.neutral.integralSections)
    (hx : rationalPoints.map Q.projection (D.neutral.reduction x) ∈
      (Dynamic.unipotent (Dynamic.oppositeCocharacter
        (Dynamic.baseChangeCocharacter (IntegralModel.residueBaseMap R) χ ≫
          Q.projection))).carrier (Over.mk (𝟙 _))) :
    {vw : rationalPoints G × rationalPoints G //
      vw.1 ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter
        (Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ ≫
          D.neutral.genericIso.hom))).carrier (Over.mk (𝟙 _)) ∧
      vw.2 ∈ (Dynamic.parabolic
        (Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ ≫
          D.neutral.genericIso.hom)).carrier (Over.mk (𝟙 _)) ∧
      D.neutral.integralPointMap x = vw.1 * vw.2} :=
  Classical.indefiniteDescription _ (by
    obtain ⟨v, hv, w, hw, he⟩ :=
      Q.generic_oppositeCell_of_quotient_unipotent hQ χ x hx
    exact ⟨(v, w), hv, hw, he⟩)

end SpecialFibreQuotientData

end Langlands.BruhatTits.IntegralModels
