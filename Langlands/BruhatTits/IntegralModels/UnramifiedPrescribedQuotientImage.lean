import Langlands.BruhatTits.IntegralModels.UnramifiedCocharacterParabolicImage
import Langlands.BruhatTits.IntegralModels.IntegralRootCentralizerGeneration
import Langlands.BruhatTits.IntegralModels.UnramifiedRootPositiveReductionStatement
import Langlands.GroupScheme.IntegralModel.ConnectedFibreDescent
import Langlands.GroupScheme.IntegralModel.HenselianReduction
import Langlands.GroupScheme.Absolute.RationalSubgroupContainment
import Langlands.GroupScheme.SchematicImageFunctoriality
import Langlands.GroupScheme.Rational.FppfQuotientSmooth

/-! # Quotient-image upper bounds along prescribed cocharacter rays -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G)
    (x : C.Apartment)
    (hN : D.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {x}))

private instance prescribedImage_neutralSmooth :
    Smooth D.neutral.group.X.hom := D.neutral_smooth

private instance prescribedImage_neutralSpecialConnected :
    ConnectedSpace D.neutral.specialFibre.X.left :=
  D.neutral.hasConnectedSpecialFibre_of_hasConnectedFibres D.neutral_connectedFibres

private instance prescribedImage_specialAffine
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G) :
    IsAffineHom N.specialFibre.X.hom :=
  MorphismProperty.pullback_snd _ _ (inferInstanceAs (IsAffineHom N.group.X.hom))

private instance prescribedImage_specialSmooth
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
    [Smooth N.group.X.hom] : Smooth N.specialFibre.X.hom :=
  MorphismProperty.pullback_snd _ _ (inferInstanceAs (Smooth N.group.X.hom))

private instance prescribedImage_specialFiniteType
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G) :
    LocallyOfFiniteType N.specialFibre.X.hom :=
  MorphismProperty.pullback_snd _ _ (inferInstanceAs (LocallyOfFiniteType N.group.X.hom))

private instance prescribedImage_henselian :
    HenselianLocalRing (fixedFieldIntegers F) :=
  (separableUnramifiedArithmetic F).2.2.2.2

private instance prescribedImage_algClosed :
    IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (fixedFieldResidueIsAlgClosure F).1

variable (A : IntegralSplitTorusData D.neutral C.i)
    (hA : IsClosedSubgroup A.inclusion)

variable (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient)
    (ν : cocharacterLattice A.specialFibreTorus)

local notation "χ" => CommGroupScheme.groupHom ν ≫
  IntegralSplitTorusData.specialFibreInclusion A
local notation "P" => Dynamic.parabolic (χ ≫ Q.projection)

omit [IsAffineHom G.X.hom] in
include hQ in
private theorem radicalPoint_maps_to_one {z : rationalPoints D.neutral.specialFibre}
    (hz : z ∈ Q.radicalPoints) : rationalPoints.map Q.projection z = 1 := by
  have hz' : z ∈
      (SubgroupFunctor.range (kernelι Q.projection)).carrier (Over.mk (𝟙 _)) := by
    rw [hQ.2.1.2.2.2]
    exact hz
  exact (mem_range_kernelι_iff Q.projection z).mp hz'

include hA in
private theorem rootSection_quotient_mem_parabolic_of_nonneg
    (a : relativeRoots C.i)
    (ha : 0 ≤ latticePairing A.specialFibreTorus (A.characterSpecialization a) ν)
    (z : (A.rootModel a a.2.1).integralSections) :
    rationalPoints.map Q.projection
        (D.neutral.reduction
          (rationalPoints.map (A.rootModelMap a a.2.1).hom z)) ∈
      (P).carrier (Over.mk (𝟙 _)) := by
  have hi : IsSplitSubtorus A.specialFibreInclusion :=
    ⟨A.specialFibreTorus_isSplit, A.specialInclusion_isClosedSubgroup
      hA⟩
  have hnz : A.characterSpecialization a ≠ 0 :=
    (A.characterSpecialization.map_ne_zero_iff).mpr a.2.1
  have hroot := RelativeRoot.subgroup_le_dynamicParabolic_of_nonneg
    A.specialFibreInclusion hi ν (A.characterSpecialization a) hnz ha
  have hz : D.neutral.reduction
      (rationalPoints.map (A.rootModelMap a a.2.1).hom z) ∈
      (RelativeRoot.subgroup A.specialFibreInclusion
        (A.characterSpecialization a)).carrier (Over.mk (𝟙 _)) := by
    have hrep := A.rootModelMap_specialFibre_isRepresentedBy a a.2.1
    have hrange : rationalPoints.map (A.rootModelMap a a.2.1).specialFibreMap
        ((A.rootModel a a.2.1).reduction z) ∈
        (SubgroupFunctor.range (A.rootModelMap a a.2.1).specialFibreMap).carrier
          (Over.mk (𝟙 _)) := ⟨(A.rootModel a a.2.1).reduction z, rfl⟩
    have hle := le_of_eq hrep.2
    rw [(A.rootModelMap a a.2.1).reduction_naturality]
    exact hle _ hrange
  exact Dynamic.parabolic_le_comap χ Q.projection _ (hroot _ hz)

private theorem centralizerSection_quotient_mem_parabolic
    (z : (A.centralizerModel C.centralizer.j C.centralizer.isRepresentedBy).integralSections) :
    rationalPoints.map Q.projection
        (D.neutral.reduction (rationalPoints.map
          (A.centralizerModelMap C.centralizer.j C.centralizer.isRepresentedBy).hom z)) ∈
      (P).carrier (Over.mk (𝟙 _)) := by
  have hz : D.neutral.reduction (rationalPoints.map
      (A.centralizerModelMap C.centralizer.j C.centralizer.isRepresentedBy).hom z) ∈
      (torusCentralizer A.specialFibreInclusion).carrier (Over.mk (𝟙 _)) := by
    rw [(A.centralizerModelMap C.centralizer.j
      C.centralizer.isRepresentedBy).reduction_naturality,
      ← (A.centralizerModelMap_specialFibre_isCentralizer
        C.centralizer.j C.centralizer.isRepresentedBy).2]
    exact ⟨(A.centralizerModel C.centralizer.j
      C.centralizer.isRepresentedBy).reduction z, rfl⟩
  exact Dynamic.parabolic_le_comap χ Q.projection _
    (Dynamic.centralizer_le_parabolic χ _
      (torusCentralizer_le_dynamicCentralizer
        A.specialFibreInclusion (CommGroupScheme.groupHom ν) _ hz))

variable (ε : ℝ) (hε : 0 < ε)

local notation "y" =>
  ε • C.cocharacterDirection
    (AddEquiv.symm (IntegralSplitTorusData.cocharacterSpecialization A) ν) +ᵥ x

include hε in
private theorem negativeRoot_ray_filtration_le_positive (a : relativeRoots C.i)
    (ha : latticePairing A.specialFibreTorus
      (A.characterSpecialization a) ν < 0) :
    C.apartment.filtration y a 0 ≤ C.apartment.filtrationPlus x a 0 := by
  rw [C.apartment.filtration_vadd]
  apply C.apartment.filtration_le_filtrationPlus
  rw [map_smul, C.rootForm_cocharacterDirection, smul_eq_mul, zero_sub]
  have hpair : latticePairing C.S a (A.cocharacterSpecialization.symm ν) =
      latticePairing A.specialFibreTorus (A.characterSpecialization a) ν := by
    simpa only [AddEquiv.apply_symm_apply] using
      (A.latticePairing_specialization a (A.cocharacterSpecialization.symm ν)).symm
  rw [hpair]
  exact neg_pos.mpr (mul_neg_of_pos_of_neg hε (by exact_mod_cast ha))

variable (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
    [Smooth M.group.X.hom] [GeometricallyConnected M.group.X.hom]
    (hM : M.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap ''
      {ε • C.cocharacterDirection
      (AddEquiv.symm (IntegralSplitTorusData.cocharacterSpecialization A) ν) +ᵥ x}))
    (φ : M.Hom D.neutral (𝟙 G))
    (B : IntegralSplitTorusData M C.i)

include hN hQ hε in
private theorem rootSection_quotient_mem_parabolic_of_negative
    (hpositive : UnramifiedRootPositiveReductionStatement.{u})
    (a : relativeRoots C.i)
    (ha : latticePairing A.specialFibreTorus (A.characterSpecialization a) ν < 0)
    (z : (A.rootModel a a.2.1).integralSections)
    (hz : rationalPoints.map (A.rootInclusion a a.2.1)
      ((A.rootModel a a.2.1).integralPointMap z) ∈ C.apartment.filtration y a 0) :
    rationalPoints.map Q.projection
      (D.neutral.reduction (rationalPoints.map (A.rootModelMap a a.2.1).hom z)) ∈
      (P).carrier (Over.mk (𝟙 _)) := by
  have hpos : D.neutral.reduction
      (rationalPoints.map (A.rootModelMap a a.2.1).hom z) ∈ Q.radicalPoints := by
    apply (hpositive F G C E {x} (Set.singleton_nonempty x)
      (fun f => by simp) D hN A Q hQ a z).mpr
    refine ⟨x, Set.mem_singleton x, ?_⟩
    exact negativeRoot_ray_filtration_le_positive
      (C := C) (D := D) (x := x) (A := A) ν ε hε a ha hz
  rw [radicalPoint_maps_to_one (D := D) Q hQ hpos]
  exact ((P).carrier (Over.mk (𝟙 _))).one_mem

include hN hA hQ hε hM φ in
omit [Smooth M.group.X.hom] [GeometricallyConnected M.group.X.hom] in
private theorem rootIntegralPoint_mem_quotientParabolic
    (hpositive : UnramifiedRootPositiveReductionStatement.{u})
    (a : relativeRoots C.i) (g : rationalPoints G)
    (hg : g ∈ M.integralPoints ⊓ rootGroupPoints C.i a) :
    g ∈
      ((((P).carrier (Over.mk (𝟙 _))).comap
        ((rationalPoints.map Q.projection).comp D.neutral.reduction)).map
          D.neutral.integralPointMap) := by
  have hgN : g ∈ D.neutral.integralPoints := by
    simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using
      φ.map_mem_integralPoints hg.1
  have hgroot : g ∈
      (A.rootModel a a.2.1).integralPoints.map
        (rationalPoints.map (A.rootInclusion a a.2.1)) := by
    rw [A.rootModel_integralPoints_eq]
    exact ⟨hgN, hg.2⟩
  have hfil : g ∈ C.apartment.filtration y a 0 := by
    have hfix : g ∈ C.apartment.rootFixer a {y} := by
      rw [← rootGroupPoints_inf_unramifiedZeroFixer_eq_rootFixer C E {y} a]
      exact ⟨hg.2, hM ▸ hg.1⟩
    rwa [C.apartment.rootFixer_singleton] at hfix
  obtain ⟨groot, hzroot, hzg⟩ := hgroot
  obtain ⟨z, hz⟩ := hzroot
  have hzg' : rationalPoints.map (A.rootInclusion a a.2.1)
      ((A.rootModel a a.2.1).integralPointMap z) = g := by
    rw [hz]
    exact hzg
  have hmem : rationalPoints.map Q.projection
      (D.neutral.reduction (rationalPoints.map (A.rootModelMap a a.2.1).hom z)) ∈
      (P).carrier (Over.mk (𝟙 _)) := by
    by_cases ha : 0 ≤ latticePairing A.specialFibreTorus
        (A.characterSpecialization a) ν
    · exact rootSection_quotient_mem_parabolic_of_nonneg
        (C := C) (D := D) (A := A) hA Q ν a ha z
    · apply rootSection_quotient_mem_parabolic_of_negative
        (C := C) (E := E) (D := D) (x := x) (hN := hN)
        (A := A) (Q := Q) (hQ := hQ) (ν := ν) (ε := ε) (hε := hε)
        hpositive a (lt_of_not_ge ha) z
      rw [hzg']
      exact hfil
  refine ⟨rationalPoints.map (A.rootModelMap a a.2.1).hom z, hmem, ?_⟩
  exact ((A.rootModelMap a a.2.1).integralPointMap_naturality z).trans hzg'

include φ in
omit [Smooth M.group.X.hom] [GeometricallyConnected M.group.X.hom] in
private theorem centralizerIntegralPoint_mem_quotientParabolic
    (g : rationalPoints G)
    (hg : g ∈ M.integralPoints ⊓ (torusCentralizer C.i).carrier (Over.mk (𝟙 _))) :
    g ∈
      ((((P).carrier (Over.mk (𝟙 _))).comap
        ((rationalPoints.map Q.projection).comp D.neutral.reduction)).map
          D.neutral.integralPointMap) := by
  have hgN : g ∈ D.neutral.integralPoints := by
    simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using
      φ.map_mem_integralPoints hg.1
  have hgcent : g ∈
      (A.centralizerModel C.centralizer.j C.centralizer.isRepresentedBy).integralPoints.map
        (rationalPoints.map C.centralizer.j) := by
    rw [A.centralizerModel_map_integralPoints_eq
      C.centralizer.j C.centralizer.isRepresentedBy]
    exact ⟨hgN, hg.2⟩
  obtain ⟨gcent, ⟨z, rfl⟩, hzg⟩ := hgcent
  refine ⟨rationalPoints.map
    (A.centralizerModelMap C.centralizer.j C.centralizer.isRepresentedBy).hom z,
    centralizerSection_quotient_mem_parabolic
      (C := C) (D := D) (A := A) Q ν z, ?_⟩
  exact ((A.centralizerModelMap C.centralizer.j
    C.centralizer.isRepresentedBy).integralPointMap_naturality z).trans hzg

include hN hA hQ hε hM φ in
omit [Smooth M.group.X.hom] [GeometricallyConnected M.group.X.hom] in
private theorem rootCentralizerIntegralPoints_le_quotientParabolic
    (hpositive : UnramifiedRootPositiveReductionStatement.{u}) :
    M.rootCentralizerIntegralPoints C.i ≤
      ((((P).carrier (Over.mk (𝟙 _))).comap
        ((rationalPoints.map Q.projection).comp D.neutral.reduction)).map
          D.neutral.integralPointMap) := by
  apply sup_le
  · apply iSup_le
    intro a g hg
    exact rootIntegralPoint_mem_quotientParabolic
      (C := C) (E := E) (D := D) (x := x) (hN := hN)
      (A := A) (hA := hA) (Q := Q) (hQ := hQ) (ν := ν)
      (ε := ε) (hε := hε) (M := M) (hM := hM) (φ := φ) hpositive a g hg
  · intro g hg
    exact centralizerIntegralPoint_mem_quotientParabolic
      (C := C) (D := D) (A := A) (Q := Q) (ν := ν) (M := M) (φ := φ) g hg

include hN hA hQ hε hM B in
/-- Conditional on the published positive-root reduction criterion, every
source integral section on a positive prescribed ray maps into the dynamic
parabolic of that cocharacter in the target reductive quotient. -/
theorem unramifiedRay_quotientReduction_mem_parabolic
    (hpositive : UnramifiedRootPositiveReductionStatement.{u})
    (s : M.integralSections) :
    rationalPoints.map Q.projection
        (D.neutral.reduction (rationalPoints.map φ.hom s)) ∈
      (P).carrier (Over.mk (𝟙 _)) := by
  let J : Subgroup D.neutral.integralSections :=
    ((P).carrier (Over.mk (𝟙 _))).comap
      ((rationalPoints.map Q.projection).comp D.neutral.reduction)
  let H : Subgroup (rationalPoints G) := J.map D.neutral.integralPointMap
  have hgen := rootCentralizerIntegralPoints_le_quotientParabolic
    (C := C) (E := E) (D := D) (x := x) (hN := hN)
    (A := A) (hA := hA) (Q := Q) (hQ := hQ) (ν := ν)
    (ε := ε) (hε := hε) (M := M) (hM := hM) (φ := φ) hpositive
  have hMint : M.integralPoints ≤ H := by
    rw [← B.rootCentralizerIntegralPoints_eq C.isConnectedReductive C.isMaximalSplitTorus]
    exact hgen
  obtain ⟨t, ht, hts⟩ := hMint (show M.integralPointMap s ∈ M.integralPoints from ⟨s, rfl⟩)
  have hts' : t = rationalPoints.map φ.hom s :=
    D.neutral.integralPointMap_injective
      (hts.trans (by simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using
        (φ.integralPointMap_naturality s).symm))
  change rationalPoints.map Q.projection (D.neutral.reduction t) ∈
    (P).carrier (Over.mk (𝟙 _)) at ht
  rw [hts'] at ht
  exact ht

include hN hA hQ hε hM B in
/-- The entire actual schematic quotient image is contained on every test
scheme in the dynamic parabolic of the prescribed residue cocharacter.
The positive-root reduction statement is an explicit remaining premise. -/
theorem unramifiedRay_quotientImage_le_parabolic
    (hpositive : UnramifiedRootPositiveReductionStatement.{u}) :
    SubgroupFunctor.range
        (SchematicImage.inclusion (φ.specialFibreMap ≫ Q.projection)) ≤ P := by
  let p := Dynamic.Affine.parabolicHom (χ ≫ Q.projection)
  have hp := Dynamic.Affine.isRepresentedBy_parabolicHom (χ ≫ Q.projection)
  rw [← hp.2]
  apply (SchematicImage.range_inclusion_le_iff
    (φ.specialFibreMap ≫ Q.projection) p
    (Dynamic.Affine.isClosedSubgroup_parabolicHom _)).mpr
  let : IsReduced M.specialFibre.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      (IsLocalRing.ResidueField (fixedFieldIntegers F)) M.specialFibre.X.left
      M.specialFibre.X.hom
  apply SubgroupFunctor.range_le_of_algClosed_points
    (Dynamic.Affine.isClosedSubgroup_parabolicHom _)
  rintro _ ⟨z, rfl⟩
  obtain ⟨s, rfl⟩ := M.reduction_surjective (inferInstanceAs (Smooth M.group.X.hom)) z
  rw [hp.2]
  change rationalPoints.map Q.projection
    (rationalPoints.map φ.specialFibreMap (M.reduction s)) ∈ (P).carrier _
  rw [← φ.reduction_naturality]
  exact unramifiedRay_quotientReduction_mem_parabolic
    (C := C) (E := E) (D := D) (x := x) (hN := hN)
    (A := A) (hA := hA) (Q := Q) (hQ := hQ) (ν := ν)
    (ε := ε) (hε := hε) (M := M) (hM := hM) (φ := φ) (B := B) hpositive s

/-- Conditional upper bound for the actual schematic quotient image along
any positive prescribed residue-cocharacter ray. -/
def HasPrescribedRayQuotientImageContainment : Prop :=
  D.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {x}) →
  IsClosedSubgroup A.inclusion → Q.IsReductiveQuotient →
  ∀ (ν : cocharacterLattice A.specialFibreTorus) (ε : ℝ), 0 < ε →
    ∀ (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
      [Smooth M.group.X.hom] [GeometricallyConnected M.group.X.hom],
      M.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap ''
        {ε • C.cocharacterDirection
          (A.cocharacterSpecialization.symm ν) +ᵥ x}) →
      ∀ (φ : M.Hom D.neutral (𝟙 G)) (B : IntegralSplitTorusData M C.i),
        UnramifiedRootPositiveReductionStatement.{u} →
          SubgroupFunctor.range
            (SchematicImage.inclusion (φ.specialFibreMap ≫ Q.projection)) ≤
          Dynamic.parabolic
            ((CommGroupScheme.groupHom ν ≫ A.specialFibreInclusion) ≫ Q.projection)

theorem hasPrescribedRayQuotientImageContainment :
    HasPrescribedRayQuotientImageContainment C E D x A Q := by
  intro hN hA hQ ν ε hε M hsm hgc hM φ B hpositive
  exact unramifiedRay_quotientImage_le_parabolic
    (C := C) (E := E) (D := D) (x := x) (hN := hN)
    (A := A) (hA := hA) (Q := Q) (hQ := hQ) (ν := ν)
    (ε := ε) (hε := hε) (M := M) (hM := hM) (φ := φ) (B := B) hpositive

end Langlands.BruhatTits.IntegralModels
