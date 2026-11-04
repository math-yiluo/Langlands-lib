import Langlands.Global.AdelicLevelModelTransition
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.NumberTheory.FunctionField

/-! # Topological targets for actual changes of adelic level -/

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

/-- Actual function-field model transitions are continuous and open, with
separated models giving open embeddings. -/
def CurvePlaceLevelModelTransitionTopologyStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S T : Finset (AlgebraicCurve.Place k F)) (hST : S ⊆ T)
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom],
    letI := curvePlaceLevelModelPointTopology k F S X
    letI := curvePlaceLevelModelPointTopology k F T
      (curvePlaceLevelModelBaseChange k F hST X)
    Continuous (curvePlaceLevelModelTransition k F hST X) ∧
      IsOpenMap (curvePlaceLevelModelTransition k F hST X) ∧
      ∀ [IsSeparated X.hom],
        IsOpenEmbedding (curvePlaceLevelModelTransition k F hST X)

/-- Actual full number-field model transitions retain all infinite factors. -/
def NumberFieldLevelModelTransitionTopologyStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S T : Finset (FinitePlace K)) (hST : S ⊆ T)
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom],
    letI := numberFieldLevelModelPointTopology K S X
    letI := numberFieldLevelModelPointTopology K T
      (numberFieldLevelModelBaseChange K hST X)
    Continuous (numberFieldLevelModelTransition K hST X) ∧
      IsOpenMap (numberFieldLevelModelTransition K hST X) ∧
      ∀ [IsSeparated X.hom],
        IsOpenEmbedding (numberFieldLevelModelTransition K hST X)

/-- The source-qualified changing-level topology properties in both characteristics. -/
def AdelicLevelModelTransitionTopologyStatement : Prop :=
  CurvePlaceLevelModelTransitionTopologyStatement.{u} ∧
    NumberFieldLevelModelTransitionTopologyStatement.{u}

end Langlands.Global
