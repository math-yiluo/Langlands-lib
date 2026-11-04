import Langlands.Global.AdelicLevelModelTopology
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.NumberTheory.FunctionField

/-! # Closed immersions on actual arithmetic-level model points -/

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Closed model immersions give closed embeddings for the actual arithmetic
level topologies, including nonaffine models and both global-field cases. -/
def AdelicLevelModelClosedImmersionStatement : Prop :=
  (∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (f : X ⟶ Y) [IsClosedImmersion f.left]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom],
    @IsClosedEmbedding
      (RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S))
      (RingPoint (curvePlaceSIntegers k F S) Y (curvePlaceAdeleLevel k F S))
      (curvePlaceLevelModelPointTopology k F S X)
      (curvePlaceLevelModelPointTopology k F S Y)
      (fun p => p ≫ f)) ∧
  (∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (f : X ⟶ Y) [IsClosedImmersion f.left]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom],
    @IsClosedEmbedding
      (RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S))
      (RingPoint ((S : Set (FinitePlace K)).integer K) Y (numberFieldAdeleLevel K S))
      (numberFieldLevelModelPointTopology K S X)
      (numberFieldLevelModelPointTopology K S Y)
      (fun p => p ≫ f))

end Langlands.Global
