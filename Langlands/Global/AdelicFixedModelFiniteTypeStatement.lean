import Langlands.Global.AdelicFixedModelPointComparisonStatement
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.NumberTheory.FunctionField

/-! # Finite-type global-field fixed-model point comparisons -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- The actual function-field comparison for finite-type arithmetic models. -/
def curvePlaceFixedModelFiniteTypeStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom],
    (∀ p : CurvePlaceFixedModelAdelePoints k F S X,
      ∃ (T : AdelicLevelIndexAbove S)
        (q : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T)),
        q.changeRing (curvePlaceAdeleLevelOverι k F S T).hom = p) ∧
    Function.Bijective (curvePlaceFixedModelPointComparison k F S X) ∧
    @IsHomeomorph (CurvePlaceFixedModelPointColimit k F S X) (CurvePlaceFixedModelAdelePoints k F S X)
      (curvePlaceFixedModelPointColimitTopology k F S X)
      (curvePlaceFixedModelAdelePointTopology k F S X)
      (curvePlaceFixedModelPointComparison k F S X)

/-- The actual full number-field comparison for finite-type arithmetic models. -/
def numberFieldFixedModelFiniteTypeStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom],
    (∀ p : NumberFieldFixedModelAdelePoints K S X,
      ∃ (T : AdelicLevelIndexAbove S)
        (q : RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T)),
        q.changeRing (numberFieldAdeleLevelOverι K S T).hom = p) ∧
    Function.Bijective (numberFieldFixedModelPointComparison K S X) ∧
    @IsHomeomorph (NumberFieldFixedModelPointColimit K S X) (NumberFieldFixedModelAdelePoints K S X)
      (numberFieldFixedModelPointColimitTopology K S X)
      (numberFieldFixedModelAdelePointTopology K S X)
      (numberFieldFixedModelPointComparison K S X)

/-- Finite-type arithmetic models in both global-field characteristics. -/
def AdelicFixedModelFiniteTypeStatement : Prop :=
  curvePlaceFixedModelFiniteTypeStatement.{u} ∧
    numberFieldFixedModelFiniteTypeStatement.{u}

end Langlands.Global
