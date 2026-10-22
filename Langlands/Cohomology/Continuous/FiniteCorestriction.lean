import Langlands.Cohomology.Continuous.QuotientSubgroupCohomology
import Langlands.Cohomology.Tate.CohomologyTransfer

universe u

open CategoryTheory

namespace Langlands.Continuous

variable {k G : Type u} [CommRing k] [Group G]

/-- Corestriction from the subgroup quotient, transported through its actual image subgroup. -/
noncomputable def quotientCorestriction (A : Rep.{u} k G) (H N : Subgroup G)
    [N.Normal] [Fintype ((G ⧸ N) ⧸ H.map (QuotientGroup.mk' N))]
    (hNH : N ≤ H) (q : ℕ) :
    groupCohomology ((Rep.res H.subtype A).quotientToInvariants (N.comap H.subtype)) q ⟶
      groupCohomology (A.quotientToInvariants N) q :=
  (quotientSubgroupCohomologyIso A H N hNH q).hom ≫
    Langlands.Tate.ordinaryCohomologyCorestriction
      (H.map (QuotientGroup.mk' N)) (A.quotientToInvariants N) q

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- Actual finite transfer at a normal quotient contained in the open subgroup. -/
noncomputable def finiteCorestriction (A : Rep.{u} k G)
    (H : OpenSubgroup G) (N : OpenNormalSubgroup G)
    (hNH : N.toSubgroup ≤ H.toSubgroup) (q : ℕ) :
    groupCohomology
        (finiteQuotientRep (Rep.res H.toSubgroup.subtype A) (restrictOpenNormal H N)) q ⟶
      groupCohomology (finiteQuotientRep A N) q := by
  letI : Finite (G ⧸ N.toSubgroup) := finite_quotient N
  letI := Fintype.ofFinite
    ((G ⧸ N.toSubgroup) ⧸ H.toSubgroup.map (QuotientGroup.mk' N.toSubgroup))
  exact quotientCorestriction A H.toSubgroup N.toSubgroup hNH q

end Langlands.Continuous
