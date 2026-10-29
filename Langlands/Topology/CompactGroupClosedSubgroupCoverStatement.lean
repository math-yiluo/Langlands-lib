import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Compactness.Compact

universe uG

namespace Langlands.Topology

/-- An increasing sequence of closed subgroups covering a compact Hausdorff
topological group contains the whole group at some index. -/
def CompactGroupClosedSubgroupCoverStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (H : ℕ → Subgroup G),
    Monotone H →
    (∀ m : ℕ, IsClosed (H m : Set G)) →
    (∀ g : G, ∃ m : ℕ, g ∈ H m) →
    ∃ m : ℕ, H m = ⊤

end Langlands.Topology
