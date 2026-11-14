import Langlands.BruhatTits.IntegralModels.IntegralTorusCentralizer
import Langlands.BruhatTits.IntegralModels.UnramifiedIncidentRootImage

/-! # Incident root images for actual neutral components of full fixer models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

private theorem neutralModelHom_comp_eq
    {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {H J : GroupScheme (Spec (CommRingCat.of K))}
    {L : IntegralModel R K H} {N P : IntegralModel R K J}
    {f : H ⟶ J} (φ : L.Hom N f) (ψ : N.Hom P (𝟙 J))
    (modelMap : L.Hom P f) : φ.hom ≫ ψ.hom = modelMap.hom := by
  apply IntegralModel.hom_eq_of_generic
  apply (cancel_mono P.genericIso.hom).mp
  rw [Functor.map_comp, Category.assoc, ψ.generic_comm,
    Category.comp_id, φ.generic_comm, modelMap.generic_comm]

private theorem neutralModelHom_specialFibre_comp_eq
    {R K : Type u} [CommRing R] [IsDomain R] [IsLocalRing R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {H J : GroupScheme (Spec (CommRingCat.of K))}
    {L : IntegralModel R K H} {N P : IntegralModel R K J}
    {f : H ⟶ J} (φ : L.Hom N f) (ψ : N.Hom P (𝟙 J))
    (modelMap : L.Hom P f) :
    φ.specialFibreMap ≫ ψ.specialFibreMap = modelMap.specialFibreMap := by
  change (GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map φ.hom ≫
    (GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map ψ.hom = _
  rw [← Functor.map_comp, neutralModelHom_comp_eq φ ψ modelMap]
  rfl

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

local instance neutralRootImage_target_smooth : Smooth M.neutral.group.X.hom :=
  M.neutral_smooth

local notation "A" => unramifiedNeutralSplitTorusData C M Ω hM

/-- The root model constructed inside the actual neutral target has its
original root fixer as its exact generic integral-point image. -/
theorem unramifiedNeutralRootModel_integralPoints_eq (a : relativeRoots C.i) :
    ((A).rootModel a a.2.1).integralPoints.map
        (rationalPoints.map ((A).rootInclusion a a.2.1)) =
      C.apartment.rootFixer a Ω := by
  rw [(A).rootModel_integralPoints_eq, inf_comm,
    rootGroupPoints_inf_unramifiedNeutral_eq_rootFixer C M Ω hM a]

/-- Smooth extension lifts the target neutral root model into the source
neutral model under the corresponding root-fixer inclusion. -/
def unramifiedNeutralRootModelLift (a : relativeRoots C.i)
    (hle : C.apartment.rootFixer a Ω ≤ C.apartment.rootFixer a Ω') :
    ((A).rootModel a a.2.1).Hom M'.neutral ((A).rootInclusion a a.2.1) :=
  Classical.choice
    ((IntegralModel.fixedField_hasSmoothHomExtension IntegralModel.smoothHomExtension F)
      ((A).rootGroup a a.2.1) G ((A).rootInclusion a a.2.1)
      ((A).rootModel a a.2.1) M'.neutral
      (IntegralModel.SplitRoot.model_isSmooth M.neutral (A).isSplit (A).inclusion
        ((A).integralCharacter a) ((A).integralCharacter_ne_zero a.2.1))
      (fun g hg => by
        have hg' : rationalPoints.map ((A).rootInclusion a a.2.1) g ∈
            C.apartment.rootFixer a Ω := by
          rw [← unramifiedNeutralRootModel_integralPoints_eq C M Ω hM a]
          exact ⟨g, hg, rfl⟩
        have hfix : C.apartment.rootFixer a Ω' ≤ M'.neutral.integralPoints := by
          rw [← rootGroupPoints_inf_unramifiedNeutral_eq_rootFixer C M' Ω' hM' a]
          exact inf_le_right
        exact hfix (hle hg')))

variable (ψ : M'.neutral.Hom M.neutral (𝟙 G))

/-- Generic rigidity identifies the lifted root map after composition with
the supplied neutral comparison. -/
theorem unramifiedNeutralRootModelLift_comp (a : relativeRoots C.i)
    (hle : C.apartment.rootFixer a Ω ≤ C.apartment.rootFixer a Ω') :
    (unramifiedNeutralRootModelLift C M M' Ω Ω' hM hM' a hle).hom ≫ ψ.hom =
      ((A).rootModelMap a a.2.1).hom :=
  neutralModelHom_comp_eq
    (unramifiedNeutralRootModelLift C M M' Ω Ω' hM hM' a hle) ψ
    ((A).rootModelMap a a.2.1)

local instance neutralRootImage_specialFibre_affine
    {H : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) H) :
    IsAffineHom N.specialFibre.X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd N.group.X.hom
      (IntegralModel.residueBaseMap (fixedFieldIntegers F)))
  exact MorphismProperty.pullback_snd _ _ N.affine

local instance neutralRootImage_specialFibre_isAffine
    {H : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) H) :
    IsAffine N.specialFibre.X.left :=
  isAffine_of_isAffineHom N.specialFibre.X.hom

/-- The actual target neutral root model factors on special fibres through
the schematic image of the neutral comparison. -/
def unramifiedNeutralRootImageFactor (a : relativeRoots C.i)
    (hle : C.apartment.rootFixer a Ω ≤ C.apartment.rootFixer a Ω') :
    ((A).rootModel a a.2.1).specialFibre ⟶ SchematicImage.image ψ.specialFibreMap :=
  (unramifiedNeutralRootModelLift C M M' Ω Ω' hM hM' a hle).specialFibreMap ≫
    SchematicImage.projection ψ.specialFibreMap

@[reassoc]
theorem unramifiedNeutralRootImageFactor_comp (a : relativeRoots C.i)
    (hle : C.apartment.rootFixer a Ω ≤ C.apartment.rootFixer a Ω') :
    unramifiedNeutralRootImageFactor C M M' Ω Ω' hM hM' ψ a hle ≫
        SchematicImage.inclusion ψ.specialFibreMap =
      ((A).rootModelMap a a.2.1).specialFibreMap := by
  unfold unramifiedNeutralRootImageFactor
  rw [Category.assoc, SchematicImage.projection_inclusion]
  exact neutralModelHom_specialFibre_comp_eq
    (unramifiedNeutralRootModelLift C M M' Ω Ω' hM hM' a hle) ψ
    ((A).rootModelMap a a.2.1)

include hM' in
/-- The entire root-model residue image is contained on every test scheme
in the actual neutral comparison image. -/
theorem unramifiedNeutralRoot_range_le_image (a : relativeRoots C.i)
    (hle : C.apartment.rootFixer a Ω ≤ C.apartment.rootFixer a Ω') :
    SubgroupFunctor.range ((A).rootModelMap a a.2.1).specialFibreMap ≤
      SubgroupFunctor.range (SchematicImage.inclusion ψ.specialFibreMap) := by
  rw [← unramifiedNeutralRootImageFactor_comp C M M' Ω Ω' hM hM' ψ a hle]
  intro T z hz
  rw [SubgroupFunctor.mem_range] at hz ⊢
  rcases hz with ⟨w, rfl⟩
  exact ⟨w ≫
    (unramifiedNeutralRootImageFactor C M M' Ω Ω' hM hM' ψ a hle).hom.hom,
    by rw [Grp.comp_hom_hom, Category.assoc]⟩

section Incident

variable {Fa Ca : Set C.Apartment}
  (hCa : AffineRootSystem.IsFacet C.affineRoots Ca)
  (hFaCa : AffineRootSystem.IsFaceOf C.affineRoots Fa Ca)
  (hΩ : Ω.Nonempty) (hΩ' : Ω'.Nonempty)
  (hsub : Ω ⊆ Fa) (hsub' : Ω' ⊆ Ca)

/-- A root positive on the adapted incident-facet cocharacter has an actual
neutral root-model factor through the comparison image. -/
def unramifiedNeutralIncidentPositiveRootImageFactor (a : relativeRoots C.i)
    (ha : 0 < latticePairing C.S a (C.incidentFacetCocharacter hCa hFaCa)) :
    ((A).rootModel a a.2.1).specialFibre ⟶ SchematicImage.image ψ.specialFibreMap :=
  unramifiedNeutralRootImageFactor C M M' Ω Ω' hM hM' ψ a
    (rootFixer_eq_of_incidentFacetCocharacter_pos_of_subsets
      C Ω Ω' hCa hFaCa hΩ hΩ' hsub hsub' a ha).le

@[reassoc]
theorem unramifiedNeutralIncidentPositiveRootImageFactor_comp (a : relativeRoots C.i)
    (ha : 0 < latticePairing C.S a (C.incidentFacetCocharacter hCa hFaCa)) :
    unramifiedNeutralIncidentPositiveRootImageFactor
        C M M' Ω Ω' hM hM' ψ hCa hFaCa hΩ hΩ' hsub hsub' a ha ≫
        SchematicImage.inclusion ψ.specialFibreMap =
      ((A).rootModelMap a a.2.1).specialFibreMap :=
  unramifiedNeutralRootImageFactor_comp C M M' Ω Ω' hM hM' ψ a _

include hM' hΩ hΩ' hsub hsub' in
/-- Every such positive neutral root-model image lies in the comparison
image as a subgroup functor on all residue-scheme tests. -/
theorem unramifiedNeutralIncidentPositiveRoot_range_le_image (a : relativeRoots C.i)
    (ha : 0 < latticePairing C.S a (C.incidentFacetCocharacter hCa hFaCa)) :
    SubgroupFunctor.range ((A).rootModelMap a a.2.1).specialFibreMap ≤
      SubgroupFunctor.range (SchematicImage.inclusion ψ.specialFibreMap) :=
  unramifiedNeutralRoot_range_le_image C M M' Ω Ω' hM hM' ψ a
    (rootFixer_eq_of_incidentFacetCocharacter_pos_of_subsets
      C Ω Ω' hCa hFaCa hΩ hΩ' hsub hsub' a ha).le

end Incident

end Langlands.BruhatTits.IntegralModels
