import Langlands.Global.AdelicFixedModelCocone
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.NumberTheory.FunctionField
import Mathlib.Topology.Maps.Proper.Basic

/-! # Proper maps on actual full-adele fixed-model points -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Properness on full-adele points after a proper function-field model has been chosen. -/
def CurvePlaceFixedModelProperMapStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsProper f.left],
    letI : TopologicalSpace (RingPoint (curvePlaceSIntegers k F S) X
      (curvePlaceAdeleOver k F S)) := curvePlaceFixedModelAdelePointTopology k F S X
    letI : TopologicalSpace (RingPoint (curvePlaceSIntegers k F S) Y
      (curvePlaceAdeleOver k F S)) := curvePlaceFixedModelAdelePointTopology k F S Y
    IsProperMap
      (X := RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleOver k F S))
      (Y := RingPoint (curvePlaceSIntegers k F S) Y (curvePlaceAdeleOver k F S))
      (fun p : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleOver k F S) =>
        (p ≫ f : RingPoint (curvePlaceSIntegers k F S) Y (curvePlaceAdeleOver k F S)))

/-- Properness on full-adele points of a proper number-field model morphism. -/
def NumberFieldFixedModelProperMapStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsProper f.left],
    letI : TopologicalSpace (RingPoint ((S : Set (FinitePlace K)).integer K) X
      (numberFieldAdeleOver K S)) := numberFieldFixedModelAdelePointTopology K S X
    letI : TopologicalSpace (RingPoint ((S : Set (FinitePlace K)).integer K) Y
      (numberFieldAdeleOver K S)) := numberFieldFixedModelAdelePointTopology K S Y
    IsProperMap
      (X := RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleOver K S))
      (Y := RingPoint ((S : Set (FinitePlace K)).integer K) Y (numberFieldAdeleOver K S))
      (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X
        (numberFieldAdeleOver K S) =>
        (p ≫ f : RingPoint ((S : Set (FinitePlace K)).integer K) Y
          (numberFieldAdeleOver K S)))

/-- Proper arithmetic model morphisms induce proper maps on actual full-adele model points. -/
def AdelicFixedModelProperMapStatement : Prop :=
  CurvePlaceFixedModelProperMapStatement.{u} ∧ NumberFieldFixedModelProperMapStatement.{u}

end Langlands.Global
