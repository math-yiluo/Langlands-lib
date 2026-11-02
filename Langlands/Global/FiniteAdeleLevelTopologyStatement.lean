import Langlands.Global.FiniteAdeleLevel
import Mathlib.Topology.Homeomorph.Defs

/-! # Topology of actual finite-adelic level rings -/

universe u

open IsDedekindDomain Topology

namespace Langlands.Global

/-- Product topology, open transitions, exhaustion and final topology for actual levels. -/
def FiniteAdeleLevelTopologyStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K],
    (∀ S, IsHomeomorph (finiteAdeleLevelProductEquiv R K S)) ∧
    (∀ (S T : Finset (HeightOneSpectrum R)) (hST : S ⊆ T),
      IsOpenEmbedding (finiteAdeleLevelMap R K hST)) ∧
    (∀ a : FiniteAdeleRing R K, ∃ S, a ∈ finiteAdeleLevel R K S) ∧
    (∀ (X : Type u) [TopologicalSpace X] (f : FiniteAdeleRing R K → X),
      Continuous f ↔ ∀ S, Continuous (f ∘ (finiteAdeleLevel R K S).subtype))

end Langlands.Global
