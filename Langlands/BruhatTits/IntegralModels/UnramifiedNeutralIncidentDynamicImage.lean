import Langlands.BruhatTits.IntegralModels.UnramifiedNeutralIncidentRootImage
import Langlands.BruhatTits.IntegralModels.UnramifiedIncidentDynamicImage

/-! # Dynamic positive subgroups in actual neutral comparison images -/

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
    (ψ : M'.neutral.Hom M.neutral (𝟙 G))
    {Fa Ca : Set C.Apartment}
    (hCa : AffineRootSystem.IsFacet C.affineRoots Ca)
    (hFaCa : AffineRootSystem.IsFaceOf C.affineRoots Fa Ca)
    (hΩ : Ω.Nonempty) (hΩ' : Ω'.Nonempty)
    (hsub : Ω ⊆ Fa) (hsub' : Ω' ⊆ Ca)

local instance neutralDynamic_target_smooth : Smooth M.neutral.group.X.hom :=
  M.neutral_smooth

local notation "A" => unramifiedNeutralSplitTorusData C M Ω hM
local notation "νs" =>
  IntegralSplitTorusData.cocharacterSpecialization
    (unramifiedNeutralSplitTorusData C M Ω hM)
    (C.incidentFacetCocharacter hCa hFaCa)
local notation "χs" => CommGroupScheme.groupHom νs ≫
  IntegralSplitTorusData.specialFibreInclusion
    (unramifiedNeutralSplitTorusData C M Ω hM)

local instance neutralDynamic_specialFibre_affine
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G) :
    IsAffineHom N.specialFibre.X.hom :=
  MorphismProperty.pullback_snd _ _ (inferInstanceAs (IsAffineHom N.group.X.hom))

local instance neutralDynamic_target_specialFibre_smooth :
    Smooth M.neutral.specialFibre.X.hom :=
  MorphismProperty.pullback_snd _ _ (inferInstanceAs (Smooth M.neutral.group.X.hom))

include hM' hΩ hΩ' hsub hsub' in
/-- The full dynamic positive subgroup for the specialized incident cocharacter
lies in the image of the actual neutral comparison on every residue test. -/
theorem unramifiedNeutralIncidentDynamicUnipotent_le_image :
    Dynamic.unipotent χs ≤
      SubgroupFunctor.range (SchematicImage.inclusion ψ.specialFibreMap) := by
  apply RelativeRoot.dynamicUnipotent_le_of_positive_rootSubgroups_le
    (A).specialFibreTorus_isSplit (A).specialFibreInclusion νs
  · intro a ha b hb hne
    exact (A).disjoint_cyclicTail_special_indivisiblePositiveRoots
      (relativeRootSystem (inertiaFixedField F) G C.isConnectedReductive
        C.S C.i C.isMaximalSplitTorus)
      C.isMaximalSplitTorus.isSplitSubtorus.1 νs ha hb hne
  · intro b hb
    let a := (A).characterSpecialization.symm b
    have he : (A).characterSpecialization a = b :=
      (A).characterSpecialization.apply_symm_apply b
    have har : a ∈ relativeRoots C.i :=
      ((A).mem_roots_characterSpecialization_iff a).mp (he.symm ▸ hb.1)
    have hpos : 0 < latticePairing C.S a (C.incidentFacetCocharacter hCa hFaCa) := by
      have hpair := (A).latticePairing_specialization a
        (C.incidentFacetCocharacter hCa hFaCa)
      rw [he] at hpair
      exact hpair ▸ hb.2
    have hrep := (A).rootModelMap_specialFibre_isRepresentedBy a har.1
    rw [← he, ← hrep.2]
    exact unramifiedNeutralIncidentPositiveRoot_range_le_image
      C M M' Ω Ω' hM hM' ψ hCa hFaCa hΩ hΩ' hsub hsub' ⟨a, har⟩ hpos

/-- Canonical inclusion of actual neutral dynamic positive points into the
neutral comparison image, retaining the same ambient residue-test point. -/
def unramifiedNeutralIncidentDynamicUnipotentImagePoints
    (T : Over (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F))))) :
    (Dynamic.unipotent χs).carrier T →*
      (SubgroupFunctor.range (SchematicImage.inclusion ψ.specialFibreMap)).carrier T :=
  Subgroup.inclusion ((unramifiedNeutralIncidentDynamicUnipotent_le_image
    C M M' Ω Ω' hM hM' ψ hCa hFaCa hΩ hΩ' hsub hsub') T)

@[simp]
theorem unramifiedNeutralIncidentDynamicUnipotentImagePoints_val
    (T : Over (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))
    (x : (Dynamic.unipotent χs).carrier T) :
    (unramifiedNeutralIncidentDynamicUnipotentImagePoints
      C M M' Ω Ω' hM hM' ψ hCa hFaCa hΩ hΩ' hsub hsub' T x).val = x.val :=
  rfl

end Langlands.BruhatTits.IntegralModels
