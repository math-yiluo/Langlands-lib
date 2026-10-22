import Langlands.Cohomology.Continuous.FiniteQuotientSystem
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-! # Zero detection for restriction to a closed normal subgroup -/

universe u

open CategoryTheory

namespace Langlands.Continuous

/-- A continuous cohomology class whose actual restriction to a closed normal
subgroup vanishes already restricts to zero on some open normal subgroup
containing that subgroup. -/
def ClosedNormalRestrictionZeroDetection : Prop :=
  ∀ (k G : Type u) [CommRing k] [TopologicalSpace k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : DiscreteModule k G) (H : ClosedSubgroup G) [H.toSubgroup.Normal] (q : ℕ)
    (x : continuousCohomology q A.toTopRep),
    continuousRestriction A H.toSubgroup q x = 0 →
      ∃ N : OpenNormalSubgroup G, H.toSubgroup ≤ N.toSubgroup ∧
        continuousRestriction A N.toSubgroup q x = 0

end Langlands.Continuous
