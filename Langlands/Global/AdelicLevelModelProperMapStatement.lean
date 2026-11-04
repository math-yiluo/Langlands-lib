import Langlands.Global.AdelicLevelModelTopology
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.NumberTheory.FunctionField
import Mathlib.Topology.Maps.Proper.Basic

/-! # Proper maps on actual arithmetic-level model points -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- The level-map ingredient of Conrad Proposition 4.4 for function fields. -/
def CurvePlaceLevelModelProperMapStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsProper f.left],
    letI : TopologicalSpace (RingPoint (curvePlaceSIntegers k F S) X
      (curvePlaceAdeleLevel k F S)) := curvePlaceLevelModelPointTopology k F S X
    letI : TopologicalSpace (RingPoint (curvePlaceSIntegers k F S) Y
      (curvePlaceAdeleLevel k F S)) := curvePlaceLevelModelPointTopology k F S Y
    IsProperMap
      (X := RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S))
      (Y := RingPoint (curvePlaceSIntegers k F S) Y (curvePlaceAdeleLevel k F S))
      (fun p : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S) =>
        (p ≫ f : RingPoint (curvePlaceSIntegers k F S) Y (curvePlaceAdeleLevel k F S)))

/-- The full number-field level-map ingredient, including infinite places. -/
def NumberFieldLevelModelProperMapStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsProper f.left],
    letI : TopologicalSpace (RingPoint ((S : Set (FinitePlace K)).integer K) X
      (numberFieldAdeleLevel K S)) := numberFieldLevelModelPointTopology K S X
    letI : TopologicalSpace (RingPoint ((S : Set (FinitePlace K)).integer K) Y
      (numberFieldAdeleLevel K S)) := numberFieldLevelModelPointTopology K S Y
    IsProperMap
      (X := RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S))
      (Y := RingPoint ((S : Set (FinitePlace K)).integer K) Y (numberFieldAdeleLevel K S))
      (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X
        (numberFieldAdeleLevel K S) =>
        (p ≫ f : RingPoint ((S : Set (FinitePlace K)).integer K) Y
          (numberFieldAdeleLevel K S)))

/-- Proper arithmetic model morphisms induce proper maps on actual level points. -/
def AdelicLevelModelProperMapStatement : Prop :=
  CurvePlaceLevelModelProperMapStatement.{u} ∧ NumberFieldLevelModelProperMapStatement.{u}

end Langlands.Global
