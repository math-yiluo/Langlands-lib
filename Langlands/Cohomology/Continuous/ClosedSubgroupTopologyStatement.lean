import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.ContinuousMap.Defs

universe u

namespace Langlands.Continuous

/-- Every continuous discrete-valued map on finite tuples of a closed subgroup of a profinite
group extends to a continuous map on ambient finite tuples. -/
def ClosedSubgroupTupleExtension : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (Y : Type u) [TopologicalSpace Y] [DiscreteTopology Y]
    (H : ClosedSubgroup G) (n : ℕ) (f : C((Fin n → H), Y)),
    ∃ F : C((Fin n → G), Y), ∀ x : Fin n → H, F (fun i => (x i : G)) = f x

/-- Two continuous discrete-valued maps on ambient finite tuples of a profinite group that agree
on all tuples from a closed normal subgroup agree on all tuples from some open normal subgroup
containing it. -/
def ClosedNormalTupleAgreement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (Y : Type u) [TopologicalSpace Y] [DiscreteTopology Y]
    (H : ClosedSubgroup G), H.toSubgroup.Normal →
    ∀ (n : ℕ) (f g : C((Fin n → G), Y)),
      (∀ x : Fin n → H, f (fun i => (x i : G)) = g (fun i => (x i : G))) →
      ∃ U : OpenNormalSubgroup G, H.toSubgroup ≤ U.toSubgroup ∧
        ∀ x : Fin n → G, (∀ i, x i ∈ U) → f x = g x

/-- Both finite-tuple approximation properties of closed subgroups of profinite groups. -/
def ClosedSubgroupTupleApproximation : Prop :=
  ClosedSubgroupTupleExtension.{u} ∧ ClosedNormalTupleAgreement.{u}

end Langlands.Continuous
