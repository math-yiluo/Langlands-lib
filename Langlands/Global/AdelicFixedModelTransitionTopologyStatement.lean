import Langlands.Global.AdelicFixedModelSystem
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.NumberTheory.FunctionField

/-! # Topology of arithmetic coefficient changes over a fixed model base -/

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Fixed-base coefficient changes for function-field models are continuous and open. -/
def CurvePlaceFixedModelTransitionTopologyStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (T U : AdelicLevelIndexAbove S) (hTU : T ≤ U),
    letI := curvePlaceFixedModelStageTopology k F S X T
    letI := curvePlaceFixedModelStageTopology k F S X U
    Continuous (RingPoint.changeRing (curvePlaceAdeleLevelOverMap k F S hTU).hom
      (X := X)) ∧
      IsOpenMap (RingPoint.changeRing (curvePlaceAdeleLevelOverMap k F S hTU).hom
        (X := X)) ∧
      ∀ [IsSeparated X.hom],
        IsOpenEmbedding
          (RingPoint.changeRing (curvePlaceAdeleLevelOverMap k F S hTU).hom (X := X))

/-- Full number-field fixed-base coefficient changes retain every infinite factor. -/
def NumberFieldFixedModelTransitionTopologyStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (T U : AdelicLevelIndexAbove S) (hTU : T ≤ U),
    letI := numberFieldFixedModelStageTopology K S X T
    letI := numberFieldFixedModelStageTopology K S X U
    Continuous (RingPoint.changeRing (numberFieldAdeleLevelOverMap K S hTU).hom
      (X := X)) ∧
      IsOpenMap (RingPoint.changeRing (numberFieldAdeleLevelOverMap K S hTU).hom
        (X := X)) ∧
      ∀ [IsSeparated X.hom],
        IsOpenEmbedding
          (RingPoint.changeRing (numberFieldAdeleLevelOverMap K S hTU).hom (X := X))

/-- The source-qualified topology of both actual fixed-base arithmetic point systems. -/
def AdelicFixedModelTransitionTopologyStatement : Prop :=
  CurvePlaceFixedModelTransitionTopologyStatement.{u} ∧
    NumberFieldFixedModelTransitionTopologyStatement.{u}

end Langlands.Global
