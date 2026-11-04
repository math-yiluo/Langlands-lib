import Langlands.Global.AdelicFixedModelCocone
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.NumberTheory.FunctionField

/-! # Open arithmetic stages in actual full-adele model points -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Actual function-field stage maps are open; their quotient images are open
subspaces, and separated models have open stage embeddings. -/
def CurvePlaceFixedModelColimitOpenStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom],
    (∀ T : AdelicLevelIndexAbove S,
      Continuous[curvePlaceFixedModelStageTopology k F S X T,
        curvePlaceFixedModelAdelePointTopology k F S X]
        (fun p : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T) =>
          p.changeRing (curvePlaceAdeleLevelOverι k F S T).hom) ∧
      @IsOpenMap _ _ (curvePlaceFixedModelStageTopology k F S X T)
        (curvePlaceFixedModelAdelePointTopology k F S X)
        (fun p : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T) =>
          p.changeRing (curvePlaceAdeleLevelOverι k F S T).hom)) ∧
    (∀ T : AdelicLevelIndexAbove S,
      @IsOpenEmbedding _ _
        (ringPointColimitStageImageTopology (curvePlaceSIntegers k F S)
          (curvePlaceAdeleLevelOverDiagram k F S) X (curvePlaceFixedModelStageTopology k F S X) T)
        (curvePlaceFixedModelAdelePointTopology k F S X)
        (fun p : RingPointColimitStageImage (curvePlaceSIntegers k F S)
          (curvePlaceAdeleLevelOverDiagram k F S) X T =>
            curvePlaceFixedModelPointComparison k F S X p.val)) ∧
    ∀ [IsSeparated X.hom] (T : AdelicLevelIndexAbove S),
      @IsOpenEmbedding _ _ (curvePlaceFixedModelStageTopology k F S X T)
        (curvePlaceFixedModelAdelePointTopology k F S X)
        (fun p : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T) =>
          p.changeRing (curvePlaceAdeleLevelOverι k F S T).hom)

/-- Full number-field stage maps are open and their quotient images are open
subspaces; separated models give open stage embeddings. -/
def NumberFieldFixedModelColimitOpenStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom],
    (∀ T : AdelicLevelIndexAbove S,
      Continuous[numberFieldFixedModelStageTopology K S X T,
        numberFieldFixedModelAdelePointTopology K S X]
        (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T) =>
          p.changeRing (numberFieldAdeleLevelOverι K S T).hom) ∧
      @IsOpenMap _ _ (numberFieldFixedModelStageTopology K S X T)
        (numberFieldFixedModelAdelePointTopology K S X)
        (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T) =>
          p.changeRing (numberFieldAdeleLevelOverι K S T).hom)) ∧
    (∀ T : AdelicLevelIndexAbove S,
      @IsOpenEmbedding _ _
        (ringPointColimitStageImageTopology ((S : Set (FinitePlace K)).integer K)
          (numberFieldAdeleLevelOverDiagram K S) X (numberFieldFixedModelStageTopology K S X) T)
        (numberFieldFixedModelAdelePointTopology K S X)
        (fun p : RingPointColimitStageImage ((S : Set (FinitePlace K)).integer K)
          (numberFieldAdeleLevelOverDiagram K S) X T =>
            numberFieldFixedModelPointComparison K S X p.val)) ∧
    ∀ [IsSeparated X.hom] (T : AdelicLevelIndexAbove S),
      @IsOpenEmbedding _ _ (numberFieldFixedModelStageTopology K S X T)
        (numberFieldFixedModelAdelePointTopology K S X)
        (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T) =>
          p.changeRing (numberFieldAdeleLevelOverι K S T).hom)

/-- The actual arithmetic open-stage assertions in both global-field characteristics. -/
def AdelicFixedModelColimitOpenStatement : Prop :=
  CurvePlaceFixedModelColimitOpenStatement.{u} ∧
    NumberFieldFixedModelColimitOpenStatement.{u}

end Langlands.Global
