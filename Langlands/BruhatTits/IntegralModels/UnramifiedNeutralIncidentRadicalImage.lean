import Langlands.BruhatTits.IntegralModels.UnramifiedNeutralIncidentParabolicImage
import Langlands.BruhatTits.IntegralModels.UnramifiedIncidentRadicalImage
import Langlands.BruhatTits.IntegralModels.SpecialFibreImageRecovery

/-! # Radical and congruence transfer for actual neutral incident models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G)
    (M M' : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G)
    (Ω Ω' : Set C.Apartment)
    (hM : M.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓
        C.pointwiseFixer (C.apartmentMap '' Ω))
    (hM' : M'.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓
        C.pointwiseFixer (C.apartmentMap '' Ω'))

/-- The full actual neutral centralizer and all strict-depth apartment root
fixers generate this subgroup of the original generic rational-point group. -/
def unramifiedNeutralPositiveRootCentralizerGroup : Subgroup (rationalPoints G) :=
  (unramifiedNeutralCentralizerModel C M Ω hM).integralPoints.map
      (rationalPoints.map C.centralizer.j) ⊔
    ⨆ a : relativeRoots C.i, C.apartment.rootFixerPlus a Ω

variable {Fa Ca : Set C.Apartment}
    (hCa : AffineRootSystem.IsFacet C.affineRoots Ca)
    (hFaCa : AffineRootSystem.IsFaceOf C.affineRoots Fa Ca)
    (hΩ : Ω.Nonempty) (hsub : Ω ⊆ Fa) (hsub' : Ω' ⊆ Ca)

include hM' hCa hFaCa hΩ hsub hsub' in
/-- The whole generated subgroup is integral in the incident source neutral
model, without identifying neutral points with a prescribed zero fixer. -/
theorem unramifiedNeutralIncidentGeneratedGroup_le_neutral :
    unramifiedNeutralPositiveRootCentralizerGroup C M Ω hM ≤
      M'.neutral.integralPoints := by
  apply sup_le
  · rintro _ ⟨z, hz, rfl⟩
    exact (unramifiedNeutralCentralizerModelMap C M' Ω' hM').map_mem_integralPoints
      (unramifiedNeutralCentralizerModel_integralPoints_le
        C M M' Ω Ω' hM hM' hΩ hz)
  · apply iSup_le
    intro a
    have hroot : C.apartment.rootFixer a Ω' ≤ M'.neutral.integralPoints := by
      rw [← rootGroupPoints_inf_unramifiedNeutral_eq_rootFixer C M' Ω' hM' a]
      exact inf_le_right
    exact (C.apartment.rootFixerPlus_le_rootFixer_of_incidentFacets_of_subsets
      C.affineRoot_mem_or_two_smul_mem hCa hFaCa hΩ hsub hsub' a).trans hroot

variable
    {U : GroupScheme
      (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F))))}
    (i : U ⟶ M.neutral.specialFibre)
    (hgen :
      ((rationalPoints.map i).range.comap M.neutral.reduction).map
          M.neutral.integralPointMap ≤
        unramifiedNeutralPositiveRootCentralizerGroup C M Ω hM)

include hM' hCa hFaCa hΩ hsub hsub' hgen in
/-- A bound on the entire target reduction preimage transfers its generic
points to the actual source neutral model. -/
theorem unramifiedNeutralIncidentReductionPreimage_le_neutral :
    ((rationalPoints.map i).range.comap M.neutral.reduction).map
        M.neutral.integralPointMap ≤ M'.neutral.integralPoints :=
  hgen.trans (unramifiedNeutralIncidentGeneratedGroup_le_neutral
    C M M' Ω Ω' hM hM' hCa hFaCa hΩ hsub hsub')

include hM' hCa hFaCa hΩ hsub hsub' hgen in
/-- The same bound contains the entire target congruence subgroup, because
the identity lies in every represented subgroup's rational-point image. -/
theorem unramifiedNeutralIncidentCongruence_le_neutral :
    M.neutral.congruenceSubgroup ≤ M'.neutral.integralPoints := by
  have hker : M.neutral.congruenceKernel ≤
      (rationalPoints.map i).range.comap M.neutral.reduction := by
    intro x hx
    change M.neutral.reduction x ∈ (rationalPoints.map i).range
    rw [(M.neutral.mem_congruenceKernel x).mp hx]
    exact (rationalPoints.map i).range.one_mem
  exact (Subgroup.map_mono hker).trans
    (unramifiedNeutralIncidentReductionPreimage_le_neutral
      C M M' Ω Ω' hM hM' hCa hFaCa hΩ hsub hsub' i hgen)

local instance neutralRadical_henselian :
    HenselianLocalRing (fixedFieldIntegers F) :=
  fixedFieldIntegersIsHenselian F

local instance neutralRadical_algClosed :
    IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (fixedFieldResidueIsAlgClosure F).1

variable (ψ : M'.neutral.Hom M.neutral (𝟙 G)) (hi : IsUnipotentRadical i)

/-- The actual full radical factors through the actual neutral comparison
image under the explicit preimage-generation bound. -/
def unramifiedNeutralIncidentRadicalImageFactor :
    U ⟶ SchematicImage.image ψ.specialFibreMap := by
  letI : Smooth U.X.hom := hi.smooth
  letI : IsReduced U.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      (IsLocalRing.ResidueField (fixedFieldIntegers F)) U.X.left U.X.hom
  exact ψ.specialFibreImageFactorOfPreimage M.neutral_smooth i
    (unramifiedNeutralIncidentReductionPreimage_le_neutral
      C M M' Ω Ω' hM hM' hCa hFaCa hΩ hsub hsub' i hgen)

include hM' hCa hFaCa hΩ hsub hsub' hgen hi in
@[reassoc]
theorem unramifiedNeutralIncidentRadicalImageFactor_comp :
    unramifiedNeutralIncidentRadicalImageFactor
        C M M' Ω Ω' hM hM' hCa hFaCa hΩ hsub hsub' i hgen ψ hi ≫
      SchematicImage.inclusion ψ.specialFibreMap = i := by
  let : Smooth U.X.hom := hi.smooth
  let : IsReduced U.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      (IsLocalRing.ResidueField (fixedFieldIntegers F)) U.X.left U.X.hom
  exact ψ.specialFibreImageFactorOfPreimage_comp M.neutral_smooth i
    (unramifiedNeutralIncidentReductionPreimage_le_neutral
      C M M' Ω Ω' hM hM' hCa hFaCa hΩ hsub hsub' i hgen)

include hM' hCa hFaCa hΩ hsub hsub' hgen hi in
/-- Radical containment holds on every residue-scheme test. -/
theorem unramifiedNeutralIncidentRadical_range_le_image :
    SubgroupFunctor.range i ≤
      SubgroupFunctor.range (SchematicImage.inclusion ψ.specialFibreMap) :=
  SubgroupFunctor.range_le_of_factor
    (unramifiedNeutralIncidentRadicalImageFactor
      C M M' Ω Ω' hM hM' hCa hFaCa hΩ hsub hsub' i hgen ψ hi)
    (unramifiedNeutralIncidentRadicalImageFactor_comp
      C M M' Ω Ω' hM hM' hCa hFaCa hΩ hsub hsub' i hgen ψ hi)

include hM' hCa hFaCa hΩ hsub hsub' hgen hi in
/-- For nonempty source subsets, the generated-radical-preimage bound gives
geometric parabolicity of the actual neutral comparison image. -/
theorem unramifiedNeutralIncidentImage_isParabolic_of_generatedPreimage
    (hΩ' : Ω'.Nonempty) :
    IsParabolicSubgroup (SchematicImage.inclusion ψ.specialFibreMap) :=
  unramifiedNeutralIncidentImage_isParabolic_of_radical_le
    C M M' Ω Ω' hM hM' ψ hCa hFaCa hΩ hΩ' hsub hsub' i hi
    (unramifiedNeutralIncidentRadical_range_le_image
      C M M' Ω Ω' hM hM' hCa hFaCa hΩ hsub hsub' i hgen ψ hi)

variable (φ : RelativeComponentModelHom M' M)

include hM' hCa hFaCa hΩ hsub hsub' hgen in
/-- A full component-model comparison has the exact reduction preimage under
the same bound, using the algebraically closed residue image projection. -/
theorem unramifiedNeutralIncident_hasParabolicReductionPreimage_of_generated :
    φ.HasParabolicReductionPreimage :=
  φ.hasParabolicReductionPreimage_of_congruence
    (unramifiedNeutralIncidentCongruence_le_neutral
      C M M' Ω Ω' hM hM' hCa hFaCa hΩ hsub hsub' i hgen)

/-- The actual source section group is identified with the full preimage of
its actual residue image, retaining the original comparison on sections. -/
def unramifiedNeutralIncidentReductionPreimageEquiv :
    M'.neutral.integralSections ≃*
      φ.specialFibreImagePoints.comap M.neutral.reduction :=
  φ.reductionPreimageMulEquiv
    (unramifiedNeutralIncidentCongruence_le_neutral
      C M M' Ω Ω' hM hM' hCa hFaCa hΩ hsub hsub' i hgen)

@[simp]
theorem unramifiedNeutralIncidentReductionPreimageEquiv_apply
    (x : M'.neutral.integralSections) :
    (unramifiedNeutralIncidentReductionPreimageEquiv
        C M M' Ω Ω' hM hM' hCa hFaCa hΩ hsub hsub' i hgen φ x :
      M.neutral.integralSections) = rationalPoints.map φ.neutral.hom x :=
  rfl

end Langlands.BruhatTits.IntegralModels
