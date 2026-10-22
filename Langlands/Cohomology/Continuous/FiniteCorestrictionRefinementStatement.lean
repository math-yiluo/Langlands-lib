import Langlands.Cohomology.Continuous.FiniteCorestriction

universe u

open CategoryTheory

namespace Langlands.Continuous

/-- Compatibility of the actual finite transfer with refinement inflation. -/
def FiniteCorestrictionRefinement : Prop :=
  ∀ (k G : Type u) [CommRing k] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] (A : Rep.{u} k G)
    (H : OpenSubgroup G) (M N : OpenNormalSubgroup G) (hMN : M ≤ N)
    (hNH : N.toSubgroup ≤ H.toSubgroup) (q : ℕ),
    finiteInflation (Rep.res H.toSubgroup.subtype A) q (restrictOpenNormal_le H hMN) ≫
        finiteCorestriction A H M (fun _ hx => hNH (hMN hx)) q =
      finiteCorestriction A H N hNH q ≫ finiteInflation A q hMN

end Langlands.Continuous
