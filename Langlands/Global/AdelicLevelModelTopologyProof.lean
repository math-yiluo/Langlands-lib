import Langlands.Global.AdelicLevelModelTopologyStatement
import Langlands.Global.AdelicFiniteTypeLevelModelComparisonProof

/-! # Proof of the actual adelic-level topology comparisons -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (C : Type u) [CommRing C] {ι : Type u} (R : ι → Type u)
variable [∀ i, CommRing (R i)] [∀ i, Algebra C (R i)]
variable [∀ i, TopologicalSpace (R i)]
variable (X : Over (Spec (CommRingCat.of C))) [IsAffine X.left]

/-- Each independently constructed local topology equals affine evaluation topology. -/
theorem localModelPointProductTopology_eq_affine :
    localModelPointProductTopology C R X =
      (inferInstance : TopologicalSpace
        (∀ i, RingPoint (R i) (ringBaseChange C (R i) X) (R i))) := by
  exact congrArg
    (fun t : ∀ i, TopologicalSpace
        (RingPoint (R i) (ringBaseChange C (R i) X) (R i)) =>
      @Pi.topologicalSpace ι _ t)
    (funext (fun i => schemePointTopology_eq_affine
      (R i) (ringBaseChange C (R i) X) (R i)))

/-- For affine models, inducing the local product topology recovers evaluation topology. -/
theorem localProductPointTopology_eq_affine [∀ i, IsTopologicalRing (R i)] :
    localProductPointTopology C R X =
      (inferInstance : TopologicalSpace (RingPoint C X (∀ i, R i))) := by
  unfold localProductPointTopology
  rw [localModelPointProductTopology_eq_affine]
  exact (localProductPointMap_isHomeomorph C R X).isInducing.eq_induced.symm

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
variable (S : Finset (AlgebraicCurve.Place k F))
variable (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))

theorem curvePlaceLevelModelPointTopology_eq_affine [IsAffine X.left] :
    curvePlaceLevelModelPointTopology k F S X =
      (inferInstance : TopologicalSpace
        (RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S))) := by
  unfold curvePlaceLevelModelPointTopology
  rw [localModelPointProductTopology_eq_affine]
  exact (curvePlaceLevelModelPointMap_isHomeomorph k F S X).isInducing.eq_induced.symm

/-- The original map with the defined level topology is a homeomorphism in the qcqs case. -/
theorem curvePlaceLevelModelPointMap_isHomeomorph_of_compact_quasiSeparated
    [CompactSpace X.left] [QuasiSeparatedSpace X.left] :
    letI := curvePlaceLevelModelPointTopology k F S X
    letI := localModelPointProductTopology (curvePlaceSIntegers k F S)
      (CurvePlaceLevelFactor k F S) X
    IsHomeomorph (curvePlaceLevelModelPointMap k F S X) := by
  let := curvePlaceLevelModelPointTopology k F S X
  let := localModelPointProductTopology (curvePlaceSIntegers k F S)
    (CurvePlaceLevelFactor k F S) X
  exact isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨⟨curvePlaceLevelModelPointMap_isInducing k F S X,
      curvePlaceLevelModelPointMap_injective k F S X⟩,
      curvePlaceLevelModelPointMap_surjective k F S X⟩

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]

/-- Finite type supplies the arithmetic bijection, and the inducing property supplies topology. -/
theorem curvePlaceLevelModelPointMap_isHomeomorph_of_finiteType
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    letI := curvePlaceLevelModelPointTopology k F S X
    letI := localModelPointProductTopology (curvePlaceSIntegers k F S)
      (CurvePlaceLevelFactor k F S) X
    IsHomeomorph (curvePlaceLevelModelPointMap k F S X) := by
  let := curvePlaceLevelModelPointTopology k F S X
  let := localModelPointProductTopology (curvePlaceSIntegers k F S)
    (CurvePlaceLevelFactor k F S) X
  have h := curvePlaceLevelModelPointMap_bijective_of_finiteType k F S X
  exact isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨⟨curvePlaceLevelModelPointMap_isInducing k F S X, h.injective⟩, h.surjective⟩

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
variable (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))

theorem numberFieldLevelModelPointTopology_eq_affine [IsAffine X.left] :
    numberFieldLevelModelPointTopology K S X =
      (inferInstance : TopologicalSpace
        (RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S))) := by
  unfold numberFieldLevelModelPointTopology
  rw [localModelPointProductTopology_eq_affine]
  exact (numberFieldLevelModelPointMap_isHomeomorph K S X).isInducing.eq_induced.symm

/-- The original full map is a homeomorphism for quasi-compact quasi-separated models. -/
theorem numberFieldLevelModelPointMap_isHomeomorph_of_compact_quasiSeparated
    [CompactSpace X.left] [QuasiSeparatedSpace X.left] :
    letI := numberFieldLevelModelPointTopology K S X
    letI := localModelPointProductTopology ((S : Set (FinitePlace K)).integer K)
      (NumberFieldLevelFactor K S) X
    IsHomeomorph (numberFieldLevelModelPointMap K S X) := by
  let := numberFieldLevelModelPointTopology K S X
  let := localModelPointProductTopology ((S : Set (FinitePlace K)).integer K)
    (NumberFieldLevelFactor K S) X
  exact isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨⟨numberFieldLevelModelPointMap_isInducing K S X,
      numberFieldLevelModelPointMap_injective K S X⟩,
      numberFieldLevelModelPointMap_surjective K S X⟩

/-- Finite type supplies the arithmetic bijection for the full number-field level. -/
theorem numberFieldLevelModelPointMap_isHomeomorph_of_finiteType
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    letI := numberFieldLevelModelPointTopology K S X
    letI := localModelPointProductTopology ((S : Set (FinitePlace K)).integer K)
      (NumberFieldLevelFactor K S) X
    IsHomeomorph (numberFieldLevelModelPointMap K S X) := by
  let := numberFieldLevelModelPointTopology K S X
  let := localModelPointProductTopology ((S : Set (FinitePlace K)).integer K)
    (NumberFieldLevelFactor K S) X
  have h := numberFieldLevelModelPointMap_bijective_of_finiteType K S X
  exact isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨⟨numberFieldLevelModelPointMap_isInducing K S X, h.injective⟩, h.surjective⟩

end NumberField

/-- The exact actual-level topology comparison in both characteristics. -/
theorem adelicLevelModelTopology : AdelicLevelModelTopologyStatement.{u} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k F _ _ _ S X
    constructor
    · intro hAffine
      exact curvePlaceLevelModelPointTopology_eq_affine k F S X
    · intro hCompact hQuasiSeparated
      exact curvePlaceLevelModelPointMap_isHomeomorph_of_compact_quasiSeparated k F S X
  · intro K _ _ S X
    constructor
    · intro hAffine
      exact numberFieldLevelModelPointTopology_eq_affine K S X
    · intro hCompact hQuasiSeparated
      exact numberFieldLevelModelPointMap_isHomeomorph_of_compact_quasiSeparated K S X
  · intro k F _ _ _ _ _ _ S X _ _
    exact curvePlaceLevelModelPointMap_isHomeomorph_of_finiteType k F S X
  · intro K _ _ S X _ _
    exact numberFieldLevelModelPointMap_isHomeomorph_of_finiteType K S X

end Langlands.Global
