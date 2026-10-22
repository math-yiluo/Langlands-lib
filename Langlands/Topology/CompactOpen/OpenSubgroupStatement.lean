import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Topology.Compactness.LocallyCompact

universe u

namespace Langlands

/-- Every open subgroup of a weakly locally compact nonarchimedean group
contains an open subgroup whose underlying set is compact. -/
def OpenSubgroupContainsCompactOpen : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
    [WeaklyLocallyCompactSpace G], ∀ H : OpenSubgroup G,
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ K ≤ H

end Langlands
