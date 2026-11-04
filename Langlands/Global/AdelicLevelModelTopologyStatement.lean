import Langlands.Global.AdelicLevelModelTopology
import Langlands.AlgebraicGeometry.PointTopology.AffineBaseChangeCoordinates
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.NumberTheory.FunctionField

/-! # Topology comparison targets for actual adelic-level model points -/

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Affine evaluation comparison and the nonaffine compact quasi-separated case,
for the original curve-place level map. -/
def CurvePlaceLevelModelTopologyStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))),
    (∀ [IsAffine X.left],
      curvePlaceLevelModelPointTopology k F S X =
        (inferInstance : TopologicalSpace
          (RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S)))) ∧
    (∀ [CompactSpace X.left] [QuasiSeparatedSpace X.left],
      letI := curvePlaceLevelModelPointTopology k F S X
      letI := localModelPointProductTopology (curvePlaceSIntegers k F S)
        (CurvePlaceLevelFactor k F S) X
      IsHomeomorph (curvePlaceLevelModelPointMap k F S X))

/-- Affine evaluation comparison and the nonaffine compact quasi-separated case,
for the original full number-field level map. -/
def NumberFieldLevelModelTopologyStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))),
    (∀ [IsAffine X.left],
      numberFieldLevelModelPointTopology K S X =
        (inferInstance : TopologicalSpace
          (RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S)))) ∧
    (∀ [CompactSpace X.left] [QuasiSeparatedSpace X.left],
      letI := numberFieldLevelModelPointTopology K S X
      letI := localModelPointProductTopology ((S : Set (FinitePlace K)).integer K)
        (NumberFieldLevelFactor K S) X
      IsHomeomorph (numberFieldLevelModelPointMap K S X))

/-- Actual finite-type curve-place models give a homeomorphism for the defined topology. -/
def CurvePlaceFiniteTypeLevelModelTopologyStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom],
    letI := curvePlaceLevelModelPointTopology k F S X
    letI := localModelPointProductTopology (curvePlaceSIntegers k F S)
      (CurvePlaceLevelFactor k F S) X
    IsHomeomorph (curvePlaceLevelModelPointMap k F S X)

/-- Actual finite-type number-field models give a homeomorphism for the defined topology. -/
def NumberFieldFiniteTypeLevelModelTopologyStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom],
    letI := numberFieldLevelModelPointTopology K S X
    letI := localModelPointProductTopology ((S : Set (FinitePlace K)).integer K)
      (NumberFieldLevelFactor K S) X
    IsHomeomorph (numberFieldLevelModelPointMap K S X)

/-- Evaluation comparison and actual nonaffine homeomorphisms in both characteristics. -/
def AdelicLevelModelTopologyStatement : Prop :=
  CurvePlaceLevelModelTopologyStatement.{u} ∧
    NumberFieldLevelModelTopologyStatement.{u} ∧
    CurvePlaceFiniteTypeLevelModelTopologyStatement.{u} ∧
    NumberFieldFiniteTypeLevelModelTopologyStatement.{u}

end Langlands.Global
