import Langlands.Cohomology.Continuous.RestrictionMaps

universe u

open CategoryTheory

namespace Langlands.Continuous

variable {k G : Type u} [CommRing k] [Group G]

/-- Transport from the subgroup quotient to its actual image in the ambient quotient,
with the genuine fixed-coefficient representation on each side. -/
noncomputable def quotientSubgroupCohomologyIso (A : Rep.{u} k G)
    (H N : Subgroup G) [N.Normal] (hNH : N ≤ H) (q : ℕ) :
    groupCohomology ((Rep.res H.subtype A).quotientToInvariants (N.comap H.subtype)) q ≅
      groupCohomology
        (Rep.res (H.map (QuotientGroup.mk' N)).subtype (A.quotientToInvariants N)) q :=
  groupCohomology.mapIso (quotientSubgroupEquiv H N)
    (fixedRestrictionEquiv A H N hNH).symm (by
      intro x
      refine QuotientGroup.induction_on x (fun g => ?_)
      ext a
      rfl) q

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to the actual image subgroup, followed by the inverse transport,
is the intrinsic restriction to the subgroup quotient. -/
theorem quotientSubgroupCohomologyIso_restriction_inv (A : Rep.{u} k G)
    (H N : Subgroup G) [N.Normal] (hNH : N ≤ H) (q : ℕ) :
    groupCohomology.map (H.map (QuotientGroup.mk' N)).subtype (𝟙 _) q ≫
        (quotientSubgroupCohomologyIso A H N hNH q).inv =
      groupCohomology.map (quotientSubgroupMap H N) (fixedSubgroupRestriction A H N) q := by
  unfold quotientSubgroupCohomologyIso
  rw [groupCohomology.mapIso_inv, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · rfl
  · rfl

/-- The forward transport converts intrinsic quotient restriction into ordinary
restriction to the image subgroup. -/
theorem quotientSubgroupCohomologyIso_restriction (A : Rep.{u} k G)
    (H N : Subgroup G) [N.Normal] (hNH : N ≤ H) (q : ℕ) :
    groupCohomology.map (quotientSubgroupMap H N) (fixedSubgroupRestriction A H N) q ≫
        (quotientSubgroupCohomologyIso A H N hNH q).hom =
      groupCohomology.map (H.map (QuotientGroup.mk' N)).subtype (𝟙 _) q := by
  rw [← quotientSubgroupCohomologyIso_restriction_inv A H N hNH q,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable [TopologicalSpace k] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- The same transport identifies the published finite-stage restriction map
with restriction to the actual image subgroup. -/
theorem finiteRestriction_quotientSubgroupCohomologyIso (A : DiscreteModule k G)
    (H : OpenSubgroup G) (N : OpenNormalSubgroup G)
    (hNH : N.toSubgroup ≤ H.toSubgroup) (q : ℕ) :
    finiteRestriction A H N q ≫
        (quotientSubgroupCohomologyIso A.toRep H.toSubgroup N.toSubgroup hNH q).hom =
      groupCohomology.map (H.toSubgroup.map (QuotientGroup.mk' N.toSubgroup)).subtype
        (𝟙 _) q :=
  quotientSubgroupCohomologyIso_restriction A.toRep H.toSubgroup N.toSubgroup hNH q

end Langlands.Continuous
