import Langlands.BruhatTits.IntegralModels.RootSpecialization
import Langlands.BruhatTits.IntegralModels.IntegralRootReductiveQuotient
import Langlands.BruhatTits.IntegralModels.IntegralTorusRootData
import Langlands.GroupScheme.Rational.RootSmoothQuotientKernel
import Langlands.BruhatTits.IntegralModels.DepthZeroReduction
import Langlands.Geometry.Building.SmoothRootModelLifting

/-! # Actual root specialization data from a surviving residue root -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace Langlands.BruhatTits.IntegralModels.IntegralTorusData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {D : RelativeComponentModelData R K G}
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    (T : IntegralTorusData D S i) (hT : IsSplitTorus T.torus.toGrp)
    (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient)
    (a : characterLattice S)
    (ha : T.characterSpecialization hT a ∈
      relativeRoots (T.specialFibreInclusion ≫ Q.projection))

private instance rootSpecializationConstruction_neutral_smooth :
    Smooth D.neutral.group.X.hom := D.neutral_smooth

private instance rootSpecializationConstruction_neutralSpecialFibre_affine :
    IsAffineHom D.neutral.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd
    D.neutral.group.X.hom (IntegralModel.residueBaseMap R))
  infer_instance

private instance rootSpecializationConstruction_neutralSpecialFibre_smooth :
    Smooth D.neutral.specialFibre.X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd
    D.neutral.group.X.hom (IntegralModel.residueBaseMap R))
  infer_instance

include ha in
/-- A character whose specialization is a quotient root is nonzero. -/
theorem ne_zero_of_characterSpecialization_mem_relativeRoots : a ≠ 0 := by
  intro h
  apply (mem_relativeRoots.1 ha).1
  rw [h, map_zero]

include ha in
/-- The specialized quotient root is nonzero. -/
theorem characterSpecialization_ne_zero_of_mem_relativeRoots :
    T.characterSpecialization hT a ≠ 0 :=
  (mem_relativeRoots.1 ha).1

include hT in
/-- The specialized split torus of the residue fibre. -/
theorem specialFibre_isSplitTorus : IsSplitTorus T.specialFibre.toGrp :=
  hT.baseChange (IntegralModel.residueBaseMap R)

include hQ ha in
/-- A chosen smooth closed representative of the residue root group of the
actual reductive quotient, for the specialized torus and character. -/
theorem exists_residueRootRepresentative :
    ∃ (V : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))
      (l : V ⟶ Q.quotient),
      (RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
        (T.characterSpecialization hT a)).IsRepresentedBy l ∧
        IsClosedSubgroup l ∧ Smooth V.X.hom := by
  have : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  exact RelativeRoot.subgroup_isSmoothClosed (T.specialFibre_isSplitTorus hT)
    (T.specialFibreInclusion ≫ Q.projection) (T.characterSpecialization hT a)
    (T.characterSpecialization_ne_zero_of_mem_relativeRoots hT Q a ha)

/-- The chosen actual residue root group. -/
def residueRootGroup :
    GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R))) :=
  Classical.choose (T.exists_residueRootRepresentative hT Q hQ a ha)

/-- Its chosen closed inclusion in the actual reductive quotient. -/
def residueRootInclusion : T.residueRootGroup hT Q hQ a ha ⟶ Q.quotient :=
  Classical.choose (Classical.choose_spec (T.exists_residueRootRepresentative hT Q hQ a ha))

theorem residueRootInclusion_spec :
    (RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
        (T.characterSpecialization hT a)).IsRepresentedBy
          (T.residueRootInclusion hT Q hQ a ha) ∧
      IsClosedSubgroup (T.residueRootInclusion hT Q hQ a ha) ∧
        Smooth (T.residueRootGroup hT Q hQ a ha).X.hom :=
  Classical.choose_spec (Classical.choose_spec
    (T.exists_residueRootRepresentative hT Q hQ a ha))

instance residueRootGroup_affine :
    IsAffineHom (T.residueRootGroup hT Q hQ a ha).X.hom := by
  have : IsClosedImmersion (T.residueRootInclusion hT Q hQ a ha).hom.hom.left :=
    (T.residueRootInclusion_spec hT Q hQ a ha).2.1
  rw [← Over.w (T.residueRootInclusion hT Q hQ a ha).hom.hom]
  infer_instance

/-- The same integral torus as compatible split-torus data for the neutral model. -/
abbrev splitData : IntegralSplitTorusData D.neutral i := T.toIntegralSplitTorusData hT

/-- The actual special-fibre inclusion of the constructed integral root model
represents the source root functor of the neutral special fibre. -/
theorem rootModelSpecialFibre_isRepresentedBy :
    (RelativeRoot.subgroup T.specialFibreInclusion
      (T.characterSpecialization hT a)).IsRepresentedBy
        ((T.splitData hT).rootModelMap a
          (T.ne_zero_of_characterSpecialization_mem_relativeRoots hT Q a ha)).specialFibreMap :=
  (T.splitData hT).rootModelMap_specialFibre_isRepresentedBy a
    (T.ne_zero_of_characterSpecialization_mem_relativeRoots hT Q a ha)

/-- The actual residue projection from the root model's special fibre to the
residue root group: the canonical root map induced by the quotient projection. -/
def residueRootProjection :
    ((T.splitData hT).rootModel a
      (T.ne_zero_of_characterSpecialization_mem_relativeRoots hT Q a ha)).specialFibre ⟶
        T.residueRootGroup hT Q hQ a ha :=
  RelativeRoot.SmoothQuotient.rootMap T.specialFibreInclusion Q.projection
    (T.characterSpecialization hT a)
    ((T.splitData hT).rootModelMap a
      (T.ne_zero_of_characterSpecialization_mem_relativeRoots hT Q a ha)).specialFibreMap
    (T.residueRootInclusion hT Q hQ a ha)
    (T.rootModelSpecialFibre_isRepresentedBy hT Q a ha)
    (T.residueRootInclusion_spec hT Q hQ a ha).1

theorem residueRootProjection_comp :
    T.residueRootProjection hT Q hQ a ha ≫ T.residueRootInclusion hT Q hQ a ha =
      ((T.splitData hT).rootModelMap a
        (T.ne_zero_of_characterSpecialization_mem_relativeRoots hT Q a ha)).specialFibreMap ≫
          Q.projection :=
  RelativeRoot.SmoothQuotient.rootMap_comp _ _ _ _ _ _ _

include hQ in
theorem residueRootProjection_kernel_smooth :
    Smooth (kernel (T.residueRootProjection hT Q hQ a ha)).X.hom := by
  have : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  exact RelativeRoot.SmoothQuotient.rootMap_kernel_smooth
    (T.specialFibre_isSplitTorus hT) T.specialFibreInclusion Q.projection
    (T.characterSpecialization hT a)
    (T.characterSpecialization_ne_zero_of_mem_relativeRoots hT Q a ha) _ _
    (T.rootModelSpecialFibre_isRepresentedBy hT Q a ha)
    (T.residueRootInclusion_spec hT Q hQ a ha).1
    (Q.projection_smooth hQ) hQ.2.1.2.1

/-- **Actual root specialization data.** For a split integral torus, a
reductive special-fibre quotient and a generic character whose
specialization is a root of that quotient, the constructed integral root
model, residue root group and residue projection form
`IntegralRootSpecializationData`. The kernel is the full kernel of the
residue projection. -/
def rootSpecializationData : IntegralRootSpecializationData T hT Q a where
  genericGroup := (T.splitData hT).rootGroup a
    (T.ne_zero_of_characterSpecialization_mem_relativeRoots hT Q a ha)
  genericInclusion := (T.splitData hT).rootInclusion a
    (T.ne_zero_of_characterSpecialization_mem_relativeRoots hT Q a ha)
  representsGenericRoot := (T.splitData hT).rootInclusion_isRootSubgroup a
    (T.ne_zero_of_characterSpecialization_mem_relativeRoots hT Q a ha)
  model := (T.splitData hT).rootModel a
    (T.ne_zero_of_characterSpecialization_mem_relativeRoots hT Q a ha)
  model_smooth := IntegralModel.SplitRoot.model_isSmooth D.neutral (T.splitData hT).isSplit
    (T.splitData hT).inclusion ((T.splitData hT).integralCharacter a)
    ((T.splitData hT).integralCharacter_ne_zero
      (T.ne_zero_of_characterSpecialization_mem_relativeRoots hT Q a ha))
  toNeutral := (T.splitData hT).rootModelMap a
    (T.ne_zero_of_characterSpecialization_mem_relativeRoots hT Q a ha)
  residueGroup := T.residueRootGroup hT Q hQ a ha
  residueProjection := T.residueRootProjection hT Q hQ a ha
  residueInclusion := T.residueRootInclusion hT Q hQ a ha
  residue_comm := T.residueRootProjection_comp hT Q hQ a ha
  residue_root := ha
  representsResidueRoot := (T.residueRootInclusion_spec hT Q hQ a ha).1
  kernel := kernel (T.residueRootProjection hT Q hQ a ha)
  kernel_smooth := T.residueRootProjection_kernel_smooth hT Q hQ a ha
  kernelInclusion := kernelι (T.residueRootProjection hT Q hQ a ha)
  kernel_closed := RelativeRoot.SmoothQuotient.kernelι_rootMap_isClosedSubgroup _ _ _ _ _ _ _
  kernel_split := by
    have : Smooth Q.quotient.X.hom := hQ.2.2.smooth
    exact (RelativeRoot.SmoothQuotient.rootMap_kernel_isSplitUnipotent
      (T.specialFibre_isSplitTorus hT) T.specialFibreInclusion Q.projection
      (T.characterSpecialization hT a)
      (T.characterSpecialization_ne_zero_of_mem_relativeRoots hT Q a ha) _ _
      (T.rootModelSpecialFibre_isRepresentedBy hT Q a ha)
      (T.residueRootInclusion_spec hT Q hQ a ha).1
      Q.radicalInclusion hQ.1.isClosedSubgroup hQ.1.smooth hQ.1.connectedSpace
      hQ.1.isNormal hQ.2.1.2.2.2).2
  isQuotient := by
    have : Smooth Q.quotient.X.hom := hQ.2.2.smooth
    exact RelativeRoot.SmoothQuotient.rootMap_isFppfQuotient
      (T.specialFibre_isSplitTorus hT) T.specialFibreInclusion Q.projection
      (T.characterSpecialization hT a)
      (T.characterSpecialization_ne_zero_of_mem_relativeRoots hT Q a ha) _ _
      (T.rootModelSpecialFibre_isRepresentedBy hT Q a ha)
      (T.residueRootInclusion_spec hT Q hQ a ha).1
      (Q.projection_smooth hQ) hQ.2.1.2.1

end Langlands.BruhatTits.IntegralModels.IntegralTorusData

namespace Langlands.BruhatTits.IntegralModels.IntegralRootSpecializationData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [HenselianLocalRing R]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {D : RelativeComponentModelData R K G}
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    {T : IntegralTorusData D S i} {hT : IsSplitTorus T.torus.toGrp}
    {Q : SpecialFibreQuotientData D} {a : characterLattice S}
    (A : IntegralRootSpecializationData T hT Q a)
    (φ : Langlands.Geometry.Building.RootFunctionFamily S G)

/-- Generic root-model points are generic points of the ambient neutral model
and of the generic root group. -/
theorem genericPoint_mem (x : A.model.integralSections) :
    rationalPoints.map A.genericInclusion (A.model.integralPointMap x) ∈
        Langlands.Geometry.Building.rootGroupPoints i a ∧
      rationalPoints.map A.genericInclusion (A.model.integralPointMap x) ∈
        D.neutral.integralPoints := by
  refine ⟨?_, ?_⟩
  · change _ ∈ (RelativeRoot.subgroup i a).carrier _
    rw [← A.representsGenericRoot.2]
    exact ⟨A.model.integralPointMap x, rfl⟩
  · rw [← A.toNeutral.integralPointMap_naturality x]
    exact ⟨_, rfl⟩

/-- **Reduction compatibility from neutral-model value bounds.** If every
neutral integral generic root point has nonnegative value, and every such point
of positive value lies in the actual positive subgroup `Q.positivePoints`, then
the supplied root model and residue projection satisfy
`RootModelReductionCompatible`. -/
theorem reductionCompatible_of_neutral (hQ : Q.IsReductiveQuotient)
    (hnonneg : ∀ g ∈ Langlands.Geometry.Building.rootGroupPoints i a,
      g ∈ D.neutral.integralPoints → (0 : WithTop ℝ) ≤ φ a g)
    (hpos : ∀ g ∈ Langlands.Geometry.Building.rootGroupPoints i a,
      g ∈ D.neutral.integralPoints → (0 : WithTop ℝ) < φ a g → g ∈ Q.positivePoints) :
    Langlands.Geometry.Building.RootModelReductionCompatible a A.genericInclusion A.model φ
      A.residueProjection := by
  refine ⟨fun x => hnonneg _ (A.genericPoint_mem x).1 (A.genericPoint_mem x).2,
    fun x hx => ?_⟩
  obtain ⟨y, hy, hyg⟩ := (Q.mem_positivePoints _).1
    (hpos _ (A.genericPoint_mem x).1 (A.genericPoint_mem x).2 hx)
  rw [← A.toNeutral.integralPointMap_naturality x] at hyg
  have hyx := D.neutral.integralPointMap_injective hyg
  have hproj : rationalPoints.map Q.projection
      (D.neutral.reduction (rationalPoints.map A.toNeutral.hom x)) = 1 := by
    rw [← hyx]
    have hker := Q.ker_projectionPoints hQ.2.1
    have hmem : D.neutral.reduction y ∈ Q.projectionPoints.ker := by
      rw [hker]
      exact hy
    exact hmem
  have hcomm := A.reduction_comm x
  rw [hproj] at hcomm
  have : Mono A.residueInclusion.hom.hom := A.representsResidueRoot.1
  apply (cancel_mono A.residueInclusion.hom.hom).1
  change rationalPoints.map A.residueInclusion
      (rationalPoints.map A.residueProjection (A.model.reduction x)) =
    (1 : rationalPoints A.residueGroup) ≫ A.residueInclusion.hom.hom
  rw [hcomm, MonObj.one_comp]

end Langlands.BruhatTits.IntegralModels.IntegralRootSpecializationData
