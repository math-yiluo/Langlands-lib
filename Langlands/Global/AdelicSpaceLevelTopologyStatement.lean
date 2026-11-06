import Langlands.Global.AdelicSpaceLevelTopology
import Langlands.Global.AdelicSpaceLevelPointsStatement
import Mathlib.NumberTheory.FunctionField
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Topological properties of adelic-level points of algebraic spaces

Conrad's claim after Corollary 5.7: for a separated algebraic space of finite type over the
`S`-integers of a global field, the topology on its adelic-level points is locally compact
and Hausdorff, and the change of level is an open embedding.
-/

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.Global

/-- The number-field case: the level points of a separated finite type space over the
`S`-integers are locally compact and Hausdorff, and every change of level `S ⊆ T` is an open
embedding into the level points of the base change to the `T`-integers. -/
def NumberFieldSpaceLevelTopologyStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))),
    IsSeparated X → FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X →
      letI := numberFieldSpaceLevelTopology K S X
      (LocallyCompactSpace
          (RingPoints ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S)) ∧
        T2Space
          (RingPoints ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S))) ∧
      ∀ (T : Finset (FinitePlace K)) (hST : S ⊆ T),
        letI := numberFieldSpaceLevelTopology K T (numberFieldSpaceLevelBaseChange K hST X)
        IsOpenEmbedding (numberFieldSpaceLevelTransition K hST X)

/-- The global function field case, for a nonempty finite set `S` of places: the level
points of a separated finite type space over the `S`-integers are locally compact and
Hausdorff, and every change of level `S ⊆ T` is an open embedding into the level points of
the base change to the `T`-integers. -/
def CurvePlaceSpaceLevelTopologyStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F)), S.Nonempty →
    ∀ X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S))),
    IsSeparated X → FiniteTypeOverRing (curvePlaceSIntegers k F S) X →
      letI := curvePlaceSpaceLevelTopology k F S X
      (LocallyCompactSpace
          (RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S)) ∧
        T2Space (RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S))) ∧
      ∀ (T : Finset (AlgebraicCurve.Place k F)) (hST : S ⊆ T),
        letI := curvePlaceSpaceLevelTopology k F T (curvePlaceSpaceLevelBaseChange k F hST X)
        IsOpenEmbedding (curvePlaceSpaceLevelTransition k F hST X)

/-- Conrad's p.17 topological claims for adelic-level points of separated finite type
algebraic spaces, for global fields of both characteristics. -/
def AdelicSpaceLevelTopologyStatement : Prop :=
  NumberFieldSpaceLevelTopologyStatement.{u} ∧ CurvePlaceSpaceLevelTopologyStatement.{u}

end Langlands.Global
