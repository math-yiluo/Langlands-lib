import Langlands.Global.NumberFieldAdeleLevel
import Mathlib.Topology.Homeomorph.Defs

/-! # Topology of actual full number-field adelic levels -/

universe u

open Topology

namespace Langlands.Global

/-- Product topology, open transitions, exhaustion and final topology for full levels. -/
def NumberFieldAdeleLevelTopologyStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K],
    (∀ S, IsHomeomorph (numberFieldAdeleLevelProductEquiv K S)) ∧
    (∀ (S T : Finset (FinitePlace K)) (hST : S ⊆ T),
      IsOpenEmbedding (numberFieldAdeleLevelMap K hST)) ∧
    (∀ a : Adeles K, ∃ S, a ∈ numberFieldAdeleLevel K S) ∧
    (∀ (X : Type u) [TopologicalSpace X] (f : Adeles K → X),
      Continuous f ↔ ∀ S, Continuous (f ∘ (numberFieldAdeleLevel K S).subtype))

end Langlands.Global
