import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Topology.Compactness.LocallyCompact

open Topology

universe u

namespace Langlands

/-- Every identity neighborhood in a weakly locally compact nonarchimedean group
contains an open subgroup whose underlying set is compact. -/
def CompactOpenSubgroupBasis : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
    [WeaklyLocallyCompactSpace G], ∀ U ∈ 𝓝 (1 : G),
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U

end Langlands
