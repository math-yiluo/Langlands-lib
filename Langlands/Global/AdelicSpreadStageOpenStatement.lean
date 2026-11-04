import Langlands.Global.AdelicGenericFiberPoints
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Maps.OpenQuotient

/-! # Open arithmetic stages in actual field-scheme adelic points -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- A function-field arithmetic stage maps openly and continuously to actual
adelic points, and embeds openly when its arithmetic model is separated.
The target topology may come from an independently specified spread. -/
def CurvePlaceSpreadStageOpenStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [PerfectField k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S U : Finset (AlgebraicCurve.Place k F))
    (M : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (N : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F U))))
    [LocallyOfFiniteType M.hom] [QuasiCompact M.hom]
    [LocallyOfFiniteType N.hom] [QuasiCompact N.hom]
    (Y : Over (Spec (CommRingCat.of F)))
    (e : curvePlaceModelGenericFiber k F S M ≅ Y)
    (f : curvePlaceModelGenericFiber k F U N ≅ Y)
    (T : AdelicLevelIndexAbove S),
    letI := curvePlaceFixedModelStageTopology k F S M T
    letI := curvePlaceSpreadAdelePointTopology k F U N Y f
    let i := fun p : RingPoint (curvePlaceSIntegers k F S) M
        (curvePlaceAdeleLevelOver k F S T) =>
      curvePlaceSpreadAdelePointEquiv k F S M Y e
        (p.changeRing (curvePlaceAdeleLevelOverι k F S T).hom)
    Continuous i ∧ IsOpenMap i ∧ ∀ [IsSeparated M.hom], IsOpenEmbedding i

/-- The full-number-field version retains all infinite factors and permits
independent spreads for the arithmetic stage and the target topology. -/
def NumberFieldSpreadStageOpenStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S U : Finset (FinitePlace K))
    (M : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (N : Over (Spec (CommRingCat.of ((U : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType M.hom] [QuasiCompact M.hom]
    [LocallyOfFiniteType N.hom] [QuasiCompact N.hom]
    (Y : Over (Spec (CommRingCat.of K)))
    (e : numberFieldModelGenericFiber K S M ≅ Y)
    (f : numberFieldModelGenericFiber K U N ≅ Y)
    (T : AdelicLevelIndexAbove S),
    letI := numberFieldFixedModelStageTopology K S M T
    letI := numberFieldSpreadAdelePointTopology K U N Y f
    let i := fun p : RingPoint ((S : Set (FinitePlace K)).integer K) M
        (numberFieldAdeleLevelOver K S T) =>
      numberFieldSpreadAdelePointEquiv K S M Y e
        (p.changeRing (numberFieldAdeleLevelOverι K S T).hom)
    Continuous i ∧ IsOpenMap i ∧ ∀ [IsSeparated M.hom], IsOpenEmbedding i

/-- Both arithmetic forms of openness of the actual stage-to-field-point map. -/
def AdelicSpreadStageOpenStatement : Prop :=
  CurvePlaceSpreadStageOpenStatement.{u} ∧ NumberFieldSpreadStageOpenStatement.{u}

end Langlands.Global
