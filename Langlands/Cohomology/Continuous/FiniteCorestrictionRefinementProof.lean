import Langlands.Cohomology.Continuous.FiniteCorestrictionRefinementStatement
import Langlands.Cohomology.Continuous.CorestrictionInflation

universe u

open CategoryTheory

namespace Langlands.Continuous

section Transport

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]

/-- The refinement transition, restricted to the actual image subgroups of `H`. -/
def imageQuotientTransition (H : Subgroup G) {M N : OpenNormalSubgroup G} (hMN : M ≤ N) :
    H.map (QuotientGroup.mk' M.toSubgroup) →* H.map (QuotientGroup.mk' N.toSubgroup) :=
  ((quotientTransition hMN).comp (H.map (QuotientGroup.mk' M.toSubgroup)).subtype).codRestrict _
    (by
      rintro ⟨_, g, hg, rfl⟩
      exact ⟨g, hg, rfl⟩)

/-- The fixed-coefficient inclusion, viewed over the image subgroups. -/
noncomputable def imageFixedTransition (A : Rep.{u} k G) (H : Subgroup G) {M N : OpenNormalSubgroup G}
    (hMN : M ≤ N) :
    Rep.res (imageQuotientTransition H hMN)
        (Rep.res (H.map (QuotientGroup.mk' N.toSubgroup)).subtype (finiteQuotientRep A N)) ⟶
      Rep.res (H.map (QuotientGroup.mk' M.toSubgroup)).subtype (finiteQuotientRep A M) :=
  Rep.ofHom
    { toLinearMap := (fixedTransition A hMN).hom.toLinearMap
      isIntertwining' x := (fixedTransition A hMN).hom.isIntertwining' x.1 }

/-- The actual subgroup-quotient transport, typed with the finite-stage representation. -/
noncomputable abbrev finiteSubgroupCohomologyIso (A : Rep.{u} k G) (H : OpenSubgroup G)
    (N : OpenNormalSubgroup G) (hNH : N.toSubgroup ≤ H.toSubgroup) (q : ℕ) :
    groupCohomology
        (finiteQuotientRep (Rep.res H.toSubgroup.subtype A) (restrictOpenNormal H N)) q ≅
      groupCohomology
        (Rep.res (H.toSubgroup.map (QuotientGroup.mk' N.toSubgroup)).subtype
          (finiteQuotientRep A N)) q :=
  quotientSubgroupCohomologyIso A H.toSubgroup N.toSubgroup hNH q

/-- Under the inverse transports to the subgroup quotients, subgroup refinement inflation
corresponds to the restricted refinement map on the image subgroups. -/
theorem finiteSubgroupCohomologyIso_inv_finiteInflation (A : Rep.{u} k G)
    (H : OpenSubgroup G) {M N : OpenNormalSubgroup G} (hMN : M ≤ N)
    (hNH : N.toSubgroup ≤ H.toSubgroup) (q : ℕ) :
    (finiteSubgroupCohomologyIso A H N hNH q).inv ≫
        finiteInflation (Rep.res H.toSubgroup.subtype A) q (restrictOpenNormal_le H hMN) =
      groupCohomology.map (imageQuotientTransition H.toSubgroup hMN)
          (imageFixedTransition A H.toSubgroup hMN) q ≫
        (finiteSubgroupCohomologyIso A H M (fun _ hx => hNH (hMN hx)) q).inv := by
  unfold finiteSubgroupCohomologyIso quotientSubgroupCohomologyIso finiteInflation
  set_option backward.isDefEq.respectTransparency false in
  rw [groupCohomology.mapIso_inv, groupCohomology.mapIso_inv, ← groupCohomology.map_comp,
    ← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · ext x
    rfl
  · rfl

/-- The same compatibility, stated with the forward transports. -/
theorem finiteInflation_finiteSubgroupCohomologyIso_hom (A : Rep.{u} k G)
    (H : OpenSubgroup G) {M N : OpenNormalSubgroup G} (hMN : M ≤ N)
    (hNH : N.toSubgroup ≤ H.toSubgroup) (q : ℕ) :
    finiteInflation (Rep.res H.toSubgroup.subtype A) q (restrictOpenNormal_le H hMN) ≫
        (finiteSubgroupCohomologyIso A H M (fun _ hx => hNH (hMN hx)) q).hom =
      (finiteSubgroupCohomologyIso A H N hNH q).hom ≫
        groupCohomology.map (imageQuotientTransition H.toSubgroup hMN)
          (imageFixedTransition A H.toSubgroup hMN) q := by
  rw [← Iso.inv_comp_eq, ← Category.assoc,
    finiteSubgroupCohomologyIso_inv_finiteInflation A H hMN hNH q, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

end Transport

/-- Corestriction from the finite stage `M` commutes with refinement inflation from `N`. -/
theorem finiteCorestrictionRefinement : FiniteCorestrictionRefinement.{u} := by
  intro k G _ _ _ _ _ A H M N hMN hNH q
  have : Finite (G ⧸ M.toSubgroup) := finite_quotient M
  have : Finite (G ⧸ N.toSubgroup) := finite_quotient N
  let : Fintype ((G ⧸ M.toSubgroup) ⧸ H.toSubgroup.map (QuotientGroup.mk' M.toSubgroup)) :=
    Fintype.ofFinite _
  let : Fintype ((G ⧸ N.toSubgroup) ⧸ H.toSubgroup.map (QuotientGroup.mk' N.toSubgroup)) :=
    Fintype.ofFinite _
  have hsurj : Function.Surjective (quotientTransition hMN) := fun x =>
    QuotientGroup.induction_on x (fun g => ⟨(g : G ⧸ M.toSubgroup), rfl⟩)
  have hK : ∀ g, g ∈ H.toSubgroup.map (QuotientGroup.mk' M.toSubgroup) ↔
      quotientTransition hMN g ∈ H.toSubgroup.map (QuotientGroup.mk' N.toSubgroup) := by
    intro g
    refine QuotientGroup.induction_on g (fun x => ?_)
    constructor
    · rintro ⟨h, hh, e⟩
      exact ⟨h, hh, by rw [← e]; rfl⟩
    · rintro ⟨h, hh, e⟩
      have hx : h⁻¹ * x ∈ N.toSubgroup := QuotientGroup.eq.mp e
      refine ⟨x, ?_, rfl⟩
      simpa using H.toSubgroup.mul_mem hh (hNH hx)
  have key := ordinaryCohomologyCorestriction_comp_map (quotientTransition hMN) hsurj
    (H.toSubgroup.map (QuotientGroup.mk' N.toSubgroup))
    (H.toSubgroup.map (QuotientGroup.mk' M.toSubgroup)) hK
    (imageQuotientTransition H.toSubgroup hMN) (fun _ => rfl)
    (finiteQuotientRep A N) (finiteQuotientRep A M) (fixedTransition A hMN)
    (imageFixedTransition A H.toSubgroup hMN) rfl q
  unfold finiteCorestriction quotientCorestriction
  set_option backward.isDefEq.respectTransparency false in
  rw [← Category.assoc, finiteInflation_finiteSubgroupCohomologyIso_hom A H hMN hNH q,
    Category.assoc, Category.assoc]
  congr 1
  exact key.symm

end Langlands.Continuous
