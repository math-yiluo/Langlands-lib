import Langlands.Global.AdelicFixedModelCocone
import Langlands.AlgebraicGeometry.PointTopology.FilteredRingPointStatement

/-! # Actual fixed-model adelic point comparisons -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- The actual curve-place comparison: equality descends under locally finite
 type; points descend and the final topologies agree under locally finite presentation. -/
def curvePlaceFixedModelPointComparisonStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))),
    (LocallyOfFiniteType X.hom →
      Function.Injective (curvePlaceFixedModelPointComparison k F S X) ∧
      (∀ (T U : AdelicLevelIndexAbove S)
        (p : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T))
        (q : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S U)),
        p.changeRing (curvePlaceAdeleLevelOverι k F S T).hom =
          q.changeRing (curvePlaceAdeleLevelOverι k F S U).hom ↔
          ∃ (V : AdelicLevelIndexAbove S) (hTV : T ≤ V) (hUV : U ≤ V),
            p.changeRing (curvePlaceAdeleLevelOverMap k F S hTV).hom =
              q.changeRing (curvePlaceAdeleLevelOverMap k F S hUV).hom) ∧
      (∀ (T : AdelicLevelIndexAbove S)
        (p q : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T)),
        p.changeRing (curvePlaceAdeleLevelOverι k F S T).hom =
          q.changeRing (curvePlaceAdeleLevelOverι k F S T).hom ↔
          ∃ (V : AdelicLevelIndexAbove S) (hTV : T ≤ V),
            p.changeRing (curvePlaceAdeleLevelOverMap k F S hTV).hom =
              q.changeRing (curvePlaceAdeleLevelOverMap k F S hTV).hom)) ∧
    (LocallyOfFinitePresentation X.hom →
      (∀ p : CurvePlaceFixedModelAdelePoints k F S X,
        ∃ (T : AdelicLevelIndexAbove S)
          (q : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T)),
          q.changeRing (curvePlaceAdeleLevelOverι k F S T).hom = p) ∧
      Function.Bijective (curvePlaceFixedModelPointComparison k F S X) ∧
      @IsHomeomorph (CurvePlaceFixedModelPointColimit k F S X) (CurvePlaceFixedModelAdelePoints k F S X)
        (curvePlaceFixedModelPointColimitTopology k F S X)
        (curvePlaceFixedModelAdelePointTopology k F S X)
        (curvePlaceFixedModelPointComparison k F S X))

/-- The actual full number-field comparison: equality descends under locally finite
 type; points descend and the final topologies agree under locally finite presentation. -/
def numberFieldFixedModelPointComparisonStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))),
    (LocallyOfFiniteType X.hom →
      Function.Injective (numberFieldFixedModelPointComparison K S X) ∧
      (∀ (T U : AdelicLevelIndexAbove S)
        (p : RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T))
        (q : RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S U)),
        p.changeRing (numberFieldAdeleLevelOverι K S T).hom =
          q.changeRing (numberFieldAdeleLevelOverι K S U).hom ↔
          ∃ (V : AdelicLevelIndexAbove S) (hTV : T ≤ V) (hUV : U ≤ V),
            p.changeRing (numberFieldAdeleLevelOverMap K S hTV).hom =
              q.changeRing (numberFieldAdeleLevelOverMap K S hUV).hom) ∧
      (∀ (T : AdelicLevelIndexAbove S)
        (p q : RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T)),
        p.changeRing (numberFieldAdeleLevelOverι K S T).hom =
          q.changeRing (numberFieldAdeleLevelOverι K S T).hom ↔
          ∃ (V : AdelicLevelIndexAbove S) (hTV : T ≤ V),
            p.changeRing (numberFieldAdeleLevelOverMap K S hTV).hom =
              q.changeRing (numberFieldAdeleLevelOverMap K S hTV).hom)) ∧
    (LocallyOfFinitePresentation X.hom →
      (∀ p : NumberFieldFixedModelAdelePoints K S X,
        ∃ (T : AdelicLevelIndexAbove S)
          (q : RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T)),
          q.changeRing (numberFieldAdeleLevelOverι K S T).hom = p) ∧
      Function.Bijective (numberFieldFixedModelPointComparison K S X) ∧
      @IsHomeomorph (NumberFieldFixedModelPointColimit K S X) (NumberFieldFixedModelAdelePoints K S X)
        (numberFieldFixedModelPointColimitTopology K S X)
        (numberFieldFixedModelAdelePointTopology K S X)
        (numberFieldFixedModelPointComparison K S X))

/-- The fixed-model point comparison for both actual arithmetic systems. -/
def AdelicFixedModelPointComparisonStatement : Prop :=
  curvePlaceFixedModelPointComparisonStatement.{u} ∧
    numberFieldFixedModelPointComparisonStatement.{u}

end Langlands.Global
