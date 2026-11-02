import Langlands.Global.CurvePlaceAdeleRing
import Mathlib.Topology.Homeomorph.Defs

/-! # Topology of actual discrete curve-place adelic levels -/

universe u

open Topology

namespace Langlands.Global

/-- Product topology, open transitions, exhaustion and final topology for concrete curve levels. -/
def CurvePlaceAdeleLevelTopologyStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F],
    (∀ S, IsHomeomorph (curvePlaceAdeleLevelProductEquiv k F S)) ∧
    (∀ (S T : Finset (AlgebraicCurve.Place k F)) (hST : S ⊆ T),
      IsOpenEmbedding (curvePlaceAdeleLevelMap k F hST)) ∧
    (∀ a : CurvePlaceAdeleRing k F, ∃ S, a ∈ curvePlaceAdeleLevel k F S) ∧
    (∀ (X : Type u) [TopologicalSpace X] (f : CurvePlaceAdeleRing k F → X),
      Continuous f ↔ ∀ S, Continuous (f ∘ (curvePlaceAdeleLevel k F S).subtype))

end Langlands.Global
