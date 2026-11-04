import Langlands.Global.AdelicGenericFiberPoints
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.NumberTheory.FunctionField
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Eventual stabilization of arithmetic stages for proper field schemes -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- For a proper function-field scheme, every sufficiently large stage of any
supplied finite-type spread is homeomorphic to the full adelic point space. -/
def CurvePlaceSpreadStabilizationStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (Y : Over (Spec (CommRingCat.of F)))
    (e : curvePlaceModelGenericFiber k F S X ≅ Y) [IsProper Y.hom],
    ∃ T : AdelicLevelIndexAbove S, ∀ U : AdelicLevelIndexAbove S, T ≤ U →
      letI := curvePlaceFixedModelStageTopology k F S X U
      letI := curvePlaceSpreadAdelePointTopology k F S X Y e
      IsHomeomorph (fun p : RingPoint (curvePlaceSIntegers k F S) X
          (curvePlaceAdeleLevelOver k F S U) =>
        curvePlaceSpreadAdelePointEquiv k F S X Y e
          (p.changeRing (curvePlaceAdeleLevelOverι k F S U).hom))

/-- Stabilization for full number-field adeles includes every infinite factor
and allows the supplied arithmetic model to be nonseparated. -/
def NumberFieldSpreadStabilizationStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (Y : Over (Spec (CommRingCat.of K)))
    (e : numberFieldModelGenericFiber K S X ≅ Y) [IsProper Y.hom],
    ∃ T : AdelicLevelIndexAbove S, ∀ U : AdelicLevelIndexAbove S, T ≤ U →
      letI := numberFieldFixedModelStageTopology K S X U
      letI := numberFieldSpreadAdelePointTopology K S X Y e
      IsHomeomorph (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X
          (numberFieldAdeleLevelOver K S U) =>
        numberFieldSpreadAdelePointEquiv K S X Y e
          (p.changeRing (numberFieldAdeleLevelOverι K S U).hom))

/-- The eventual-stage assertion of Conrad Proposition 4.4 in both characteristics. -/
def AdelicSpreadStabilizationStatement : Prop :=
  CurvePlaceSpreadStabilizationStatement.{u} ∧
    NumberFieldSpreadStabilizationStatement.{u}

end Langlands.Global
