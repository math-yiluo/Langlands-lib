import Langlands.Global.AdelicLevelModelTopology
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemePullbackPoints

/-! # Pullbacks of actual arithmetic-level model point spaces -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Actual curve-place level points preserve arbitrary relative pullback cones,
with the existing level topologies and the compatible-pair subspace topology. -/
def CurvePlaceLevelModelPullbackStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X Y Z : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (f : X ⟶ Z) (g : Y ⟶ Z) (c : PullbackCone f g), IsLimit c →
    letI : TopologicalSpace
        (RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S)) :=
      curvePlaceLevelModelPointTopology k F S X
    letI : TopologicalSpace
        (RingPoint (curvePlaceSIntegers k F S) Y (curvePlaceAdeleLevel k F S)) :=
      curvePlaceLevelModelPointTopology k F S Y
    @IsHomeomorph
      (RingPoint (curvePlaceSIntegers k F S) c.pt (curvePlaceAdeleLevel k F S))
      {q : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S) ×
        RingPoint (curvePlaceSIntegers k F S) Y (curvePlaceAdeleLevel k F S) //
        q.1 ≫ f = q.2 ≫ g}
      (curvePlaceLevelModelPointTopology k F S c.pt) inferInstance
      (affineSchemePullbackPointComparison
        (curvePlaceSIntegers k F S) (curvePlaceAdeleLevel k F S) c)

/-- Actual full number-field level points preserve arbitrary relative pullback
cones, retaining every infinite factor and the original integer scalars. -/
def NumberFieldLevelModelPullbackStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X Y Z : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (f : X ⟶ Z) (g : Y ⟶ Z) (c : PullbackCone f g), IsLimit c →
    letI : TopologicalSpace
        (RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S)) :=
      numberFieldLevelModelPointTopology K S X
    letI : TopologicalSpace
        (RingPoint ((S : Set (FinitePlace K)).integer K) Y (numberFieldAdeleLevel K S)) :=
      numberFieldLevelModelPointTopology K S Y
    @IsHomeomorph
      (RingPoint ((S : Set (FinitePlace K)).integer K) c.pt (numberFieldAdeleLevel K S))
      {q : RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S) ×
        RingPoint ((S : Set (FinitePlace K)).integer K) Y (numberFieldAdeleLevel K S) //
        q.1 ≫ f = q.2 ≫ g}
      (numberFieldLevelModelPointTopology K S c.pt) inferInstance
      (affineSchemePullbackPointComparison
        ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K S) c)

/-- The two actual arithmetic-level pullback comparisons are homeomorphisms. -/
def AdelicLevelModelPullbackStatement : Prop :=
  CurvePlaceLevelModelPullbackStatement.{u} ∧ NumberFieldLevelModelPullbackStatement.{u}

end Langlands.Global
