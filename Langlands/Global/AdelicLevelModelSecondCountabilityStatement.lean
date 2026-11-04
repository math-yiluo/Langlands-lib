import Langlands.Global.AdelicLevelModelTopology
import Mathlib.NumberTheory.FunctionField
import Mathlib.Topology.Bases

/-! # Second countability of actual arithmetic-level model points -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- The actual function-field level points have a countable base. -/
def CurvePlaceLevelModelSecondCountabilityStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom],
    @SecondCountableTopology
      (RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S))
      (curvePlaceLevelModelPointTopology k F S X)

/-- The actual full number-field level points have a countable base. -/
def NumberFieldLevelModelSecondCountabilityStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom],
    @SecondCountableTopology
      (RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S))
      (numberFieldLevelModelPointTopology K S X)

/-- Second countability in both global-field characteristics, without separation. -/
def AdelicLevelModelSecondCountabilityStatement : Prop :=
  CurvePlaceLevelModelSecondCountabilityStatement.{u} ∧
    NumberFieldLevelModelSecondCountabilityStatement.{u}

end Langlands.Global
