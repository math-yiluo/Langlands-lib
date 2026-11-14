import Langlands.BruhatTits.IntegralModels.ResidueCocharacterIncidentFacet
import Langlands.BruhatTits.IntegralModels.UnramifiedIncidentRootImage
import Langlands.BruhatTits.IntegralModels.UnramifiedZeroFixerRootSupport
import Langlands.BruhatTits.IntegralModels.UnramifiedZeroFixerCentralizerImage
import Langlands.GroupScheme.Rational.NonnegativeRootParabolicGeneration
import Langlands.GroupScheme.HomImage

/-! # Prescribed residue cocharacters in actual incident comparison images -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

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
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
    [Smooth N.group.X.hom] [ConnectedSpace N.specialFibre.X.left]
    (Ω : Set C.Apartment)
    (hN : N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))

local notation "A" => unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN

private instance cocharacterImage_specialFibre_affine
    (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G) :
    IsAffineHom M.specialFibre.X.hom :=
  MorphismProperty.pullback_snd _ _ (inferInstanceAs (IsAffineHom M.group.X.hom))

private instance cocharacterImage_specialFibre_smooth : Smooth N.specialFibre.X.hom :=
  MorphismProperty.pullback_snd _ _ (inferInstanceAs (Smooth N.group.X.hom))

/-- Nonnegative fixer containment for an arbitrary actual residue cocharacter
puts its whole dynamic parabolic in the actual schematic comparison image. -/
theorem unramifiedCocharacterDynamicParabolic_le_image_of_rootFixers_le
    (ν : cocharacterLattice (A).specialFibreTorus)
    (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
    (Ω' : Set C.Apartment)
    (hM : M.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω'))
    (φ : M.Hom N (𝟙 G)) (hΩ : Ω.Nonempty)
    (hfix : ∀ a : relativeRoots C.i,
      0 ≤ latticePairing (A).specialFibreTorus ((A).characterSpecialization a) ν →
      C.apartment.rootFixer a Ω ≤ C.apartment.rootFixer a Ω') :
    Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ (A).specialFibreInclusion) ≤
      SubgroupFunctor.range (SchematicImage.inclusion φ.specialFibreMap) := by
  have hi : IsSplitSubtorus (A).specialFibreInclusion :=
    ⟨(A).specialFibreTorus_isSplit, (A).specialInclusion_isClosedSubgroup
      (unramifiedZeroFixerIntegralSplitTorusData_isClosedSubgroup C E N Ω hN)⟩
  apply RelativeRoot.dynamicParabolic_le_of_nonnegative_rootSubgroups_le
    (A).specialFibreInclusion hi ν (SchematicImage.inclusion φ.specialFibreMap)
    (HomImage.isClosedSubgroup_inclusion φ.specialFibreMap)
  · exact unramifiedZeroFixer_specialCentralizer_le_image C E N M Ω Ω' hN hM hΩ φ
  · intro b hb hpair
    let a := (A).characterSpecialization.symm b
    have he : (A).characterSpecialization a = b :=
      (A).characterSpecialization.apply_symm_apply b
    have ha : a ∈ relativeRoots C.i :=
      ((A).mem_roots_characterSpecialization_iff a).mp (he.symm ▸ hb)
    have hrep := (A).rootModelMap_specialFibre_isRepresentedBy a ha.1
    rw [← he, ← hrep.2]
    apply unramifiedZeroFixerRoot_range_le_image C E N M Ω Ω' hN hM φ ⟨a, ha⟩
    exact hfix ⟨a, ha⟩ (he.symm ▸ hpair)

/-- A positive ray in every prescribed residue-cocharacter direction selects
an incident facet whose actual comparison images contain the prescribed
full dynamic parabolic. Nonempty portions of either facet are allowed. -/
theorem exists_pos_incidentFacet_dynamicParabolic_le_images
    (x : C.Apartment) (hΩ : Ω.Nonempty)
    (hsub : Ω ⊆ AffineRootSystem.facet C.affineRoots x)
    (ν : cocharacterLattice (A).specialFibreTorus) :
    let w := C.cocharacterDirection ((A).cocharacterSpecialization.symm ν)
    ∃ ε : ℝ, 0 < ε ∧
      AffineRootSystem.IsFaceOf C.affineRoots
        (AffineRootSystem.facet C.affineRoots x)
        (AffineRootSystem.facet C.affineRoots (ε • w +ᵥ x)) ∧
      ∀ (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
        (Ω' : Set C.Apartment), Ω'.Nonempty →
        Ω' ⊆ AffineRootSystem.facet C.affineRoots (ε • w +ᵥ x) →
        M.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω') →
        ∀ φ : M.Hom N (𝟙 G),
          Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ (A).specialFibreInclusion) ≤
            SubgroupFunctor.range (SchematicImage.inclusion φ.specialFibreMap) := by
  dsimp only
  obtain ⟨ε, hε, hface, _, hfix⟩ :=
    (A).exists_pos_incidentFacet_of_specialFibreCocharacter C x ν
  refine ⟨ε, hε, hface, ?_⟩
  intro M Ω' hΩ' hsub' hM φ
  apply unramifiedCocharacterDynamicParabolic_le_image_of_rootFixers_le
    C E N Ω hN ν M Ω' hM φ hΩ
  intro a ha
  rw [C.apartment.rootFixer_eq_of_nonempty_subset_facet
      C.affineRoot_mem_or_two_smul_mem (AffineRootSystem.isFacet_facet _ _) hΩ hsub a,
    C.apartment.rootFixer_eq_of_nonempty_subset_facet
      C.affineRoot_mem_or_two_smul_mem (AffineRootSystem.isFacet_facet _ _) hΩ' hsub' a,
    hfix a ha]

/-- Every actual residue cocharacter has an incident ray with dynamic
parabolic containment for all actual zero-fixer comparison images. -/
def HasPrescribedCocharacterIncidentParabolicContainment : Prop :=
  ∀ (x : C.Apartment), Ω.Nonempty →
    Ω ⊆ AffineRootSystem.facet C.affineRoots x →
    ∀ ν : cocharacterLattice (A).specialFibreTorus,
      let w := C.cocharacterDirection ((A).cocharacterSpecialization.symm ν)
      ∃ ε : ℝ, 0 < ε ∧
        AffineRootSystem.IsFaceOf C.affineRoots
          (AffineRootSystem.facet C.affineRoots x)
          (AffineRootSystem.facet C.affineRoots (ε • w +ᵥ x)) ∧
        ∀ (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
          (Ω' : Set C.Apartment), Ω'.Nonempty →
          Ω' ⊆ AffineRootSystem.facet C.affineRoots (ε • w +ᵥ x) →
          M.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω') →
          ∀ φ : M.Hom N (𝟙 G),
            Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ (A).specialFibreInclusion) ≤
              SubgroupFunctor.range (SchematicImage.inclusion φ.specialFibreMap)

theorem hasPrescribedCocharacterIncidentParabolicContainment :
    HasPrescribedCocharacterIncidentParabolicContainment C E N Ω hN := by
  intro x hΩ hsub ν
  exact exists_pos_incidentFacet_dynamicParabolic_le_images C E N Ω hN x hΩ hsub ν

end Langlands.BruhatTits.IntegralModels
