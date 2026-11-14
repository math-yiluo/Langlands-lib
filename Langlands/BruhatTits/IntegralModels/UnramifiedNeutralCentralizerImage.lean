import Langlands.BruhatTits.IntegralModels.UnramifiedNeutralCentralizerComparison
import Langlands.BruhatTits.IntegralModels.UnramifiedZeroFixerCentralizerImage
import Langlands.GroupScheme.IntegralModel.GenericRigidity
import Langlands.GroupScheme.HomImage

/-! # Full residue centralizers in actual neutral comparison images -/

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

private theorem centralizerModelHom_comp_eq
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

private theorem centralizerModelHom_specialFibre_comp_eq
    {R K : Type u} [CommRing R] [IsDomain R] [IsLocalRing R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {H J : GroupScheme (Spec (CommRingCat.of K))}
    {L : IntegralModel R K H} {N P : IntegralModel R K J}
    {f : H ⟶ J} (φ : L.Hom N f) (ψ : N.Hom P (𝟙 J))
    (modelMap : L.Hom P f) :
    φ.specialFibreMap ≫ ψ.specialFibreMap = modelMap.specialFibreMap := by
  change (GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map φ.hom ≫
    (GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map ψ.hom = _
  rw [← Functor.map_comp, centralizerModelHom_comp_eq φ ψ modelMap]
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

/-- Smooth homomorphism extension lifts the actual target neutral centralizer
into the source neutral model, provided the target subset is nonempty. -/
def unramifiedNeutralCentralizerLift (hΩ : Ω.Nonempty) :
    (unramifiedNeutralCentralizerModel C M Ω hM).Hom M'.neutral C.centralizer.j :=
  Classical.choice
    ((IntegralModel.fixedField_hasSmoothHomExtension IntegralModel.smoothHomExtension F)
      C.centralizer.Z G C.centralizer.j
      (unramifiedNeutralCentralizerModel C M Ω hM) M'.neutral
      (unramifiedNeutralCentralizerModel_isSmooth C M Ω hM)
      (fun _ hz =>
        (unramifiedNeutralCentralizerModelMap C M' Ω' hM').map_mem_integralPoints
          (unramifiedNeutralCentralizerModel_integralPoints_le
            C M M' Ω Ω' hM hM' hΩ hz)))

variable (ψ : M'.neutral.Hom M.neutral (𝟙 G))

/-- The lifted centralizer's composite with the comparison is the original
closed target-centralizer inclusion. -/
theorem unramifiedNeutralCentralizerLift_comp (hΩ : Ω.Nonempty) :
    (unramifiedNeutralCentralizerLift C M M' Ω Ω' hM hM' hΩ).hom ≫ ψ.hom =
      (unramifiedNeutralCentralizerModelMap C M Ω hM).hom :=
  centralizerModelHom_comp_eq
    (unramifiedNeutralCentralizerLift C M M' Ω Ω' hM hM' hΩ) ψ
    (unramifiedNeutralCentralizerModelMap C M Ω hM)

/-- The same compatibility holds on the actual residue fibres. -/
theorem unramifiedNeutralCentralizerLift_specialFibre_comp (hΩ : Ω.Nonempty) :
    (unramifiedNeutralCentralizerLift C M M' Ω Ω' hM hM' hΩ).specialFibreMap ≫
        ψ.specialFibreMap =
      (unramifiedNeutralCentralizerModelMap C M Ω hM).specialFibreMap :=
  centralizerModelHom_specialFibre_comp_eq
    (unramifiedNeutralCentralizerLift C M M' Ω Ω' hM hM' hΩ) ψ
    (unramifiedNeutralCentralizerModelMap C M Ω hM)

local instance neutralCentralizerImage_specialFibre_affine
    {H : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) H) :
    IsAffineHom N.specialFibre.X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd N.group.X.hom
      (IntegralModel.residueBaseMap (fixedFieldIntegers F)))
  exact MorphismProperty.pullback_snd _ _ N.affine

local instance neutralCentralizerImage_specialFibre_isAffine
    {H : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) H) :
    IsAffine N.specialFibre.X.left :=
  isAffine_of_isAffineHom N.specialFibre.X.hom

/-- The entire actual target centralizer's residue fibre factors through
the schematic image of the generic-identity neutral comparison. -/
def unramifiedNeutralCentralizerImageFactor (hΩ : Ω.Nonempty) :
    (unramifiedNeutralCentralizerModel C M Ω hM).specialFibre ⟶
      SchematicImage.image ψ.specialFibreMap :=
  (unramifiedNeutralCentralizerLift C M M' Ω Ω' hM hM' hΩ).specialFibreMap ≫
    SchematicImage.projection ψ.specialFibreMap

@[reassoc]
theorem unramifiedNeutralCentralizerImageFactor_comp (hΩ : Ω.Nonempty) :
    unramifiedNeutralCentralizerImageFactor C M M' Ω Ω' hM hM' ψ hΩ ≫
        SchematicImage.inclusion ψ.specialFibreMap =
      (unramifiedNeutralCentralizerModelMap C M Ω hM).specialFibreMap := by
  unfold unramifiedNeutralCentralizerImageFactor
  rw [Category.assoc, SchematicImage.projection_inclusion]
  exact unramifiedNeutralCentralizerLift_specialFibre_comp C M M' Ω Ω' hM hM' ψ hΩ

local instance neutralCentralizerImage_target_smooth : Smooth M.neutral.group.X.hom :=
  M.neutral_smooth

include hM' in
/-- The full centralizer of the actual residue torus is contained in the
actual neutral comparison image on every residue-scheme test. -/
theorem unramifiedNeutral_specialCentralizer_le_image (hΩ : Ω.Nonempty) :
    torusCentralizer
        (T := (unramifiedNeutralSplitTorusData C M Ω hM).specialFibreTorus)
        (unramifiedNeutralSplitTorusData C M Ω hM).specialFibreInclusion ≤
      SubgroupFunctor.range (SchematicImage.inclusion ψ.specialFibreMap) := by
  have hrep := IntegralSplitTorusData.centralizerModelMap_specialFibre_isCentralizer
    (unramifiedNeutralSplitTorusData C M Ω hM)
    C.centralizer.j C.centralizer.isRepresentedBy
  rw [← hrep.2]
  exact SubgroupFunctor.range_le_of_factor
    (unramifiedNeutralCentralizerImageFactor C M M' Ω Ω' hM hM' ψ hΩ)
    (unramifiedNeutralCentralizerImageFactor_comp C M M' Ω Ω' hM hM' ψ hΩ)

end Langlands.BruhatTits.IntegralModels
