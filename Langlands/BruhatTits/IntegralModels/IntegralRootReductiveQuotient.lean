import Langlands.BruhatTits.IntegralModels.ReductiveQuotientRoots
import Langlands.BruhatTits.IntegralModels.IntegralRootSpecialFibre
import Langlands.BruhatTits.IntegralModels.SpecialFibre
import Langlands.GroupScheme.Rational.RootSmoothQuotient
import Langlands.GroupScheme.Rational.RootSubgroupRepresentability
import Langlands.GroupScheme.Lie.SchematicImage

/-! # Actual integral root maps into the same model's reductive quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace Langlands.BruhatTits.IntegralModels

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {D : RelativeComponentModelData R K G}

private instance integralRootQuotient_neutralSpecialFibre_affine :
    IsAffineHom D.neutral.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd
    D.neutral.group.X.hom (IntegralModel.residueBaseMap R))
  infer_instance

private instance integralRootQuotient_neutral_smooth :
    Smooth D.neutral.group.X.hom := D.neutral_smooth

private instance integralRootQuotient_neutralSpecialFibre_smooth :
    Smooth D.neutral.specialFibre.X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd
    D.neutral.group.X.hom (IntegralModel.residueBaseMap R))
  infer_instance

namespace IntegralSplitTorusData

variable {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    (A : IntegralSplitTorusData D.neutral i) (Q : SpecialFibreQuotientData D)

/-- The actual special-fibre root map followed by the actual radical projection. -/
def rootReductiveQuotientMap (a : characterLattice S) (ha : a ≠ 0) :
    (A.rootModel a ha).specialFibre ⟶ Q.quotient :=
  (A.rootModelMap a ha).specialFibreMap ≫ Q.projection

private instance integralRootQuotient_rootSpecialFibre_affine
    (a : characterLattice S) (ha : a ≠ 0) :
    IsAffineHom (A.rootModel a ha).specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd
    (A.rootModel a ha).group.X.hom (IntegralModel.residueBaseMap R))
  infer_instance

private instance rootSpecialFibre_smooth (a : characterLattice S) (ha : a ≠ 0) :
    Smooth (A.rootModel a ha).specialFibre.X.hom := by
  let : Smooth (A.rootModel a ha).group.X.hom :=
    IntegralModel.SplitRoot.model_isSmooth D.neutral A.isSplit A.inclusion
      (A.integralCharacter a) (A.integralCharacter_ne_zero ha)
  change Smooth (CategoryTheory.Limits.pullback.snd
    (A.rootModel a ha).group.X.hom (IntegralModel.residueBaseMap R))
  infer_instance

private instance rootSpecialFibre_connected (a : characterLattice S) (ha : a ≠ 0) :
    ConnectedSpace (A.rootModel a ha).specialFibre.X.left :=
  (A.rootModel a ha).hasConnectedSpecialFibre_of_geometricallyConnected
    ((A.rootModel a ha).hasGeometricallyConnectedSpecialFibre_of_geometricallyConnected
      (IntegralModel.SplitRoot.model_hasGeometricallyConnectedFibres
        D.neutral A.isSplit A.inclusion
        (A.integralCharacter a) (A.integralCharacter_ne_zero ha)))

/-- The full kernel of the original root-to-quotient map is smooth. -/
theorem rootReductiveQuotientMap_smooth_kernel (hQ : Q.IsReductiveQuotient)
    (a : characterLattice S) (ha : a ≠ 0) :
    Smooth (kernel (A.rootReductiveQuotientMap Q a ha)).X.hom := by
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  have hχ : A.characterSpecialization a ≠ 0 :=
    by simpa only [map_zero] using A.characterSpecialization.injective.ne ha
  obtain ⟨V, l, hl, _, _⟩ := RelativeRoot.subgroup_isSmoothClosed
    A.specialFibreTorus_isSplit (A.specialFibreInclusion ≫ Q.projection)
    (A.characterSpecialization a) hχ
  exact RelativeRoot.SmoothQuotient.smooth_kernel_comp
    A.specialFibreTorus_isSplit A.specialFibreInclusion Q.projection
    (A.characterSpecialization a) hχ (A.rootModelMap a ha).specialFibreMap l
    (A.rootModelMap_specialFibre_isRepresentedBy a ha) hl
    (Q.projection_smooth hQ) hQ.2.1.2.1

/-- The original differential has exactly the full target cyclic weight span. -/
theorem rootReductiveQuotientMap_lie_range (hQ : Q.IsReductiveQuotient)
    (a : characterLattice S) (ha : a ≠ 0) :
    LinearMap.range (Lie.targetMapLinear (A.rootReductiveQuotientMap Q a ha)
      (IsLocalRing.ResidueField R)) =
        RelativeRoot.semigroupWeightSpan
          (AutomorphicAction.conjugation (A.specialFibreInclusion ≫ Q.projection))
          (RelativeRoot.cyclicTail (A.characterSpecialization a) 1) := by
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  exact RelativeRoot.SmoothQuotient.lie_range_comp
    A.specialFibreTorus_isSplit A.specialFibreInclusion Q.projection
    (A.characterSpecialization a)
    (by simpa only [map_zero] using A.characterSpecialization.injective.ne ha)
    (A.rootModelMap a ha).specialFibreMap
    (A.rootModelMap_specialFibre_isRepresentedBy a ha) (Q.projection_smooth hQ)

local instance rootImage_lieCommGroup (a : characterLattice S) (ha : a ≠ 0) :
    CommGroup (lieKernel (SchematicImage.image (A.rootReductiveQuotientMap Q a ha))
      (IsLocalRing.ResidueField R)) :=
  lieKernelCommGroup _

local instance rootImage_lieModule (a : characterLattice S) (ha : a ≠ 0) :
    Module (IsLocalRing.ResidueField R)
      (Additive (lieKernel (SchematicImage.image (A.rootReductiveQuotientMap Q a ha))
        (IsLocalRing.ResidueField R))) :=
  lieKernelModule _

/-- The Lie algebra of the actual schematic image has that same cyclic image. -/
theorem rootReductiveQuotientImage_lie_range (hQ : Q.IsReductiveQuotient)
    (a : characterLattice S) (ha : a ≠ 0) :
    LinearMap.range (Lie.targetMapLinear
      (SchematicImage.inclusion (A.rootReductiveQuotientMap Q a ha))
      (IsLocalRing.ResidueField R)) =
        RelativeRoot.semigroupWeightSpan
          (AutomorphicAction.conjugation (A.specialFibreInclusion ≫ Q.projection))
          (RelativeRoot.cyclicTail (A.characterSpecialization a) 1) := by
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  rw [Lie.range_schematicImage_inclusion_of_smooth_kernel
    (A.rootReductiveQuotientMap Q a ha)
    (A.rootReductiveQuotientMap_smooth_kernel Q hQ a ha)]
  exact A.rootReductiveQuotientMap_lie_range Q hQ a ha

end IntegralSplitTorusData

end Langlands.BruhatTits.IntegralModels
