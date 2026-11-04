import Langlands.Global.AdelicLevelModelTopology
import Mathlib.NumberTheory.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Topology.Compactness.LocallyCompact

/-! # Local compactness of actual arithmetic-level model points -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Corollary 3.7 for actual function fields with finite constants. -/
def CurvePlaceLevelModelLocalCompactnessStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom],
    letI := curvePlaceLevelModelPointTopology k F S X
    LocallyCompactSpace
      (RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S)) ∧
    (∀ [IsSeparated X.hom],
      T2Space (RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S)))

/-- Corollary 3.7 for full number-field levels, including all infinite factors. -/
def NumberFieldLevelModelLocalCompactnessStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom],
    letI := numberFieldLevelModelPointTopology K S X
    LocallyCompactSpace
      (RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S)) ∧
    (∀ [IsSeparated X.hom],
      T2Space
        (RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S)))

/-- Actual arithmetic-level points are locally compact, and separated models give
Hausdorff spaces, in both global-field characteristics. -/
def AdelicLevelModelLocalCompactnessStatement : Prop :=
  CurvePlaceLevelModelLocalCompactnessStatement.{u} ∧
    NumberFieldLevelModelLocalCompactnessStatement.{u}

end Langlands.Global
