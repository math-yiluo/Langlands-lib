import Langlands.BruhatTits.IntegralModels.IntegralQuotientKernelRootCentralizerGeneration
import Langlands.BruhatTits.IntegralModels.UnramifiedNeutralCongruence
import Langlands.BruhatTits.IntegralModels.SpecialFibrePositiveDescent

/-! # Radical preimages and incident images of actual neutral models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G)
    (M : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G)
    (Ω : Set C.Apartment)
    (hM : M.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓
        C.pointwiseFixer (C.apartmentMap '' Ω))
    {Fa : Set C.Apartment}
    (hFa : AffineRootSystem.IsFacet C.affineRoots Fa)
    (hΩ : Ω.Nonempty) (hsub : Ω ⊆ Fa)
    (Q : SpecialFibreQuotientData M) (hQ : Q.IsReductiveQuotient)

include hM hFa hΩ hsub hQ in
/-- The entire actual radical preimage is bounded by the actual neutral
centralizer and all strict-depth root fixers on a nonempty facet subset. -/
theorem unramifiedNeutralPositivePoints_le_positiveRootCentralizerGroup :
    Q.positivePoints ≤ unramifiedNeutralPositiveRootCentralizerGroup C M Ω hM := by
  let : Smooth M.neutral.group.X.hom := M.neutral_smooth
  let : GeometricallyConnected M.neutral.group.X.hom := M.neutral_geometricallyConnected
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  let : ConnectedSpace Q.quotient.X.left := hQ.2.2.connectedSpace
  have hkernel := Q.hasSmoothConnectedUnipotentKernel hQ
  let : ConnectedSpace (Langlands.GroupScheme.kernel Q.projection).X.left := hkernel.2.1
  let A := unramifiedNeutralSplitTorusData C M Ω hM
  rw [Q.positivePoints_eq_specialFibreKernelPoints hQ.2.1]
  apply A.specialFibreKernelPoints_le_of_roots_and_centralizer Q.projection
    (Q.projection_smooth hQ) hQ.2.1.2.1 hkernel.2.2
    C.isConnectedReductive C.isMaximalSplitTorus
  · intro a
    rw [← Q.positivePoints_eq_specialFibreKernelPoints hQ.2.1]
    exact (unramifiedNeutralPositivePoints_inf_rootGroupPoints_le_rootFixerPlus
      C M Ω hM hFa hΩ hsub Q hQ a).trans
        (le_sup_of_le_right (le_iSup (fun a : relativeRoots C.i =>
          C.apartment.rootFixerPlus a Ω) a))
  · rw [← Q.positivePoints_eq_specialFibreKernelPoints hQ.2.1]
    have hcent :
        M.neutral.integralPoints ⊓ (torusCentralizer C.i).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of (inertiaFixedField F))))) =
          (unramifiedNeutralCentralizerModel C M Ω hM).integralPoints.map
            (rationalPoints.map C.centralizer.j) :=
      (A.centralizerModel_map_integralPoints_eq
        C.centralizer.j C.centralizer.isRepresentedBy).symm
    exact (inf_le_inf_right _ Q.positivePoints_le_integralPoints).trans
      (hcent.le.trans le_sup_left)

variable
    (M' : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G)
    (Ω' : Set C.Apartment)
    (hM' : M'.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓
        C.pointwiseFixer (C.apartmentMap '' Ω'))
    {Ca : Set C.Apartment}
    (hCa : AffineRootSystem.IsFacet C.affineRoots Ca)
    (hFaCa : AffineRootSystem.IsFaceOf C.affineRoots Fa Ca)
    (hsub' : Ω' ⊆ Ca)
    (ψ : M'.neutral.Hom M.neutral (𝟙 G))

include hM hM' hCa hFaCa hΩ hsub hsub' hQ in
/-- The whole actual radical preimage is integral in an incident source
neutral model, with the generation bound proved from the facet geometry. -/
theorem unramifiedNeutralIncidentPositivePoints_le_neutral :
    Q.positivePoints ≤ M'.neutral.integralPoints :=
  (unramifiedNeutralPositivePoints_le_positiveRootCentralizerGroup
    C M Ω hM hFaCa.1 hΩ hsub Q hQ).trans
      (unramifiedNeutralIncidentGeneratedGroup_le_neutral
        C M M' Ω Ω' hM hM' hCa hFaCa hΩ hsub hsub')

/-- The actual radical factors through the actual incident neutral comparison
image without an extra radical-preimage generation premise. -/
def unramifiedNeutralIncidentFacetRadicalImageFactor :
    Q.radical ⟶ SchematicImage.image ψ.specialFibreMap :=
  unramifiedNeutralIncidentRadicalImageFactor
    C M M' Ω Ω' hM hM' hCa hFaCa hΩ hsub hsub' Q.radicalInclusion
    (unramifiedNeutralPositivePoints_le_positiveRootCentralizerGroup
      C M Ω hM hFaCa.1 hΩ hsub Q hQ) ψ hQ.1

include hM hM' hCa hFaCa hΩ hsub hsub' hQ in
@[reassoc]
theorem unramifiedNeutralIncidentFacetRadicalImageFactor_comp :
    unramifiedNeutralIncidentFacetRadicalImageFactor
      C M Ω hM hΩ hsub Q hQ M' Ω' hM' hCa hFaCa hsub' ψ ≫
      SchematicImage.inclusion ψ.specialFibreMap = Q.radicalInclusion :=
  unramifiedNeutralIncidentRadicalImageFactor_comp
    C M M' Ω Ω' hM hM' hCa hFaCa hΩ hsub hsub' Q.radicalInclusion
    (unramifiedNeutralPositivePoints_le_positiveRootCentralizerGroup
      C M Ω hM hFaCa.1 hΩ hsub Q hQ) ψ hQ.1

include hM hM' hCa hFaCa hΩ hsub hsub' hQ in
/-- The actual radical is contained in the incident neutral comparison image
on every residue-scheme test. -/
theorem unramifiedNeutralIncidentFacetRadical_range_le_image :
    SubgroupFunctor.range Q.radicalInclusion ≤
      SubgroupFunctor.range (SchematicImage.inclusion ψ.specialFibreMap) :=
  SubgroupFunctor.range_le_of_factor
    (unramifiedNeutralIncidentFacetRadicalImageFactor
      C M Ω hM hΩ hsub Q hQ M' Ω' hM' hCa hFaCa hsub' ψ)
    (unramifiedNeutralIncidentFacetRadicalImageFactor_comp
      C M Ω hM hΩ hsub Q hQ M' Ω' hM' hCa hFaCa hsub' ψ)

include hM hM' hCa hFaCa hΩ hsub hsub' hQ in
/-- The actual neutral image of a generic-identity incident comparison is
parabolic when both subsets are nonempty, without a generation premise. -/
theorem unramifiedNeutralIncidentImage_isParabolic_of_facet
    (hΩ' : Ω'.Nonempty) :
    IsParabolicSubgroup (SchematicImage.inclusion ψ.specialFibreMap) :=
  unramifiedNeutralIncidentImage_isParabolic_of_generatedPreimage
    C M M' Ω Ω' hM hM' hCa hFaCa hΩ hsub hsub' Q.radicalInclusion
    (unramifiedNeutralPositivePoints_le_positiveRootCentralizerGroup
      C M Ω hM hFaCa.1 hΩ hsub Q hQ) ψ hQ.1 hΩ'

end Langlands.BruhatTits.IntegralModels
