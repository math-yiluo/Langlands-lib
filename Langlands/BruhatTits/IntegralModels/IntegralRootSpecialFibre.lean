import Langlands.BruhatTits.IntegralModels.IntegralRootFiltration
import Langlands.GroupScheme.Rational.RootSubgroupLieImage

/-! # Actual special fibres and Lie images of integral root models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.BruhatTits.IntegralModels.IntegralSplitTorusData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    {S : CommGroupScheme (Spec (CommRingCat.of K))}
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {i : S.toGrp ⟶ G} {N : IntegralModel R K G}
    (A : IntegralSplitTorusData N i)

/-- The actual residue fibre of the supplied integral split torus. -/
abbrev specialFibreTorus : CommGroupScheme
    (Spec (CommRingCat.of (IsLocalRing.ResidueField R))) :=
  (CommGroupScheme.baseChange (IntegralModel.residueBaseMap R)).obj A.torus

/-- Its actual map into the ambient special fibre. -/
def specialFibreInclusion : A.specialFibreTorus.toGrp ⟶ N.specialFibre :=
  (GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map A.inclusion

/-- Generic-to-residue character specialization through the supplied
integral split torus and its specified generic identification. -/
def characterSpecialization : characterLattice S ≃+ characterLattice A.specialFibreTorus :=
  (characterLattice.congr A.genericIso).symm.trans
    ((characterLattice.baseChangeEquiv (Spec.algebraMap R K) A.torus A.isSplit).symm.trans
      (characterLattice.baseChangeEquiv (IntegralModel.residueBaseMap R) A.torus A.isSplit))

@[simp] theorem characterSpecialization_apply (a : characterLattice S) :
    A.characterSpecialization a =
      characterLattice.baseChange (IntegralModel.residueBaseMap R) A.torus
        (A.integralCharacter a) := rfl

theorem specialFibreTorus_isSplit : IsSplitTorus A.specialFibreTorus.toGrp :=
  A.isSplit.baseChange (IntegralModel.residueBaseMap R)

variable [Smooth N.group.X.hom]

local instance ambientSpecialFibre_affine : IsAffineHom N.specialFibre.X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd N.group.X.hom (IntegralModel.residueBaseMap R))
  infer_instance

local instance ambientSpecialFibre_smooth : Smooth N.specialFibre.X.hom := by
  change Smooth
    (CategoryTheory.Limits.pullback.snd N.group.X.hom (IntegralModel.residueBaseMap R))
  infer_instance

local instance rootSpecialFibre_affine (a : characterLattice S) (ha : a ≠ 0) :
    IsAffineHom (A.rootModel a ha).specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd
    (A.rootModel a ha).group.X.hom (IntegralModel.residueBaseMap R))
  infer_instance

/-- The actual special-fibre inclusion represents the full root functor
for the specialized character, on every residue-field scheme test. -/
theorem rootModelMap_specialFibre_isRepresentedBy (a : characterLattice S) (ha : a ≠ 0) :
    (RelativeRoot.subgroup A.specialFibreInclusion
      (A.characterSpecialization a)).IsRepresentedBy
        (A.rootModelMap a ha).specialFibreMap := by
  have hrep : (RelativeRoot.subgroup A.inclusion (A.integralCharacter a)).IsRepresentedBy
      (A.rootModelMap a ha).hom :=
    (IntegralModel.SplitRoot.integral_properties N A.isSplit A.inclusion
      (A.integralCharacter a) (A.integralCharacter_ne_zero ha)).1
  have hbase := hrep.baseChange (IntegralModel.residueBaseMap R)
  rw [← RelativeRoot.subgroup_baseChange] at hbase
  exact hbase

theorem rootModelMap_specialFibre_isClosedSubgroup (a : characterLattice S) (ha : a ≠ 0) :
    IsClosedSubgroup (A.rootModelMap a ha).specialFibreMap :=
  (A.rootModelMap_isClosedSubgroup a ha).baseChange (IntegralModel.residueBaseMap R)

/-- The actual differential image of this special-fibre inclusion is
exactly the sum of the positive integer-multiple weight spaces. -/
theorem rootModelMap_specialFibre_lie_range (a : characterLattice S) (ha : a ≠ 0) :
    LinearMap.range (Lie.targetMapLinear (A.rootModelMap a ha).specialFibreMap
      (IsLocalRing.ResidueField R)) =
        RelativeRoot.semigroupWeightSpan
          (AutomorphicAction.conjugation A.specialFibreInclusion)
          (RelativeRoot.cyclicTail (A.characterSpecialization a) 1) := by
  have hrep := A.rootModelMap_specialFibre_isRepresentedBy a ha
  have : Mono (A.rootModelMap a ha).specialFibreMap.hom.hom := hrep.1
  rw [← RelativeRoot.tangentSubmodule_range, hrep.2]
  exact RelativeRoot.tangentSubmodule_subgroup A.specialFibreInclusion
    (A.characterSpecialization a) A.specialFibreTorus_isSplit
      (by simpa only [map_zero] using A.characterSpecialization.injective.ne ha)

/-- The Lie algebra of the actual root-model special fibre, identified by
its differential with the positive cyclic ambient weight span. -/
def rootSpecialFibreLieEquiv (a : characterLattice S) (ha : a ≠ 0) :
    Additive (lieKernel (A.rootModel a ha).specialFibre (IsLocalRing.ResidueField R)) ≃ₗ[
      IsLocalRing.ResidueField R]
        RelativeRoot.semigroupWeightSpan
          (AutomorphicAction.conjugation A.specialFibreInclusion)
          (RelativeRoot.cyclicTail (A.characterSpecialization a) 1) := by
  have : Mono (A.rootModelMap a ha).specialFibreMap.hom.hom :=
    (A.rootModelMap_specialFibre_isRepresentedBy a ha).1
  exact (LinearEquiv.ofInjective
    (Lie.targetMapLinear (A.rootModelMap a ha).specialFibreMap (IsLocalRing.ResidueField R))
    (Lie.targetMapLinear_injective _ _)).trans
      (LinearEquiv.ofEq _ _ (A.rootModelMap_specialFibre_lie_range a ha))

@[simp] theorem rootSpecialFibreLieEquiv_apply_coe
    (a : characterLattice S) (ha : a ≠ 0)
    (X : Additive (lieKernel (A.rootModel a ha).specialFibre (IsLocalRing.ResidueField R))) :
    ((A.rootSpecialFibreLieEquiv a ha X).val :
      Additive (lieKernel N.specialFibre (IsLocalRing.ResidueField R))) =
        Lie.targetMapLinear (A.rootModelMap a ha).specialFibreMap
          (IsLocalRing.ResidueField R) X := rfl

end Langlands.BruhatTits.IntegralModels.IntegralSplitTorusData
