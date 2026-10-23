import Langlands.Cohomology.Continuous.CorestrictionLawsStatement
import Langlands.Cohomology.Continuous.OrdinaryTransferLawsProof
import Langlands.Cohomology.Continuous.CorestrictionInflation

universe u

open CategoryTheory

namespace Langlands.Continuous

namespace FiniteTower

set_option backward.isDefEq.respectTransparency false

variable {k G : Type u} [CommRing k] [Group G]

/-- The inner quotient image is the inverse image of the nested ambient quotient image. -/
theorem image_mem_iff (K H N : Subgroup G) [N.Normal] (_h : K ≤ H) (hNK : N ≤ K)
    (x : H ⧸ N.comap H.subtype) :
    x ∈ (K.subgroupOf H).map (QuotientGroup.mk' (N.comap H.subtype)) ↔
      quotientSubgroupEquiv H N x ∈
        (K.map (QuotientGroup.mk' N)).subgroupOf (H.map (QuotientGroup.mk' N)) := by
  refine QuotientGroup.induction_on x (fun g => ?_)
  constructor
  · rintro ⟨y, hy, e⟩
    refine ⟨y.1, hy, ?_⟩
    exact congrArg (quotientSubgroupMap H N) e
  · rintro ⟨y, hy, e⟩
    have he : y⁻¹ * g.1 ∈ N := QuotientGroup.eq.mp e
    have hg : g.1 ∈ K := by
      simpa using K.mul_mem hy (hNK he)
    exact ⟨g, hg, rfl⟩

/-- Restriction of the quotient equivalence to the inner image subgroup. -/
noncomputable def imageMap (K H N : Subgroup G) [N.Normal] (h : K ≤ H) (hNK : N ≤ K) :
    (K.subgroupOf H).map (QuotientGroup.mk' (N.comap H.subtype)) →*
      (K.map (QuotientGroup.mk' N)).subgroupOf (H.map (QuotientGroup.mk' N)) :=
  ((quotientSubgroupEquiv H N).toMonoidHom.comp
    ((K.subgroupOf H).map (QuotientGroup.mk' (N.comap H.subtype))).subtype).codRestrict _
      (fun x => (image_mem_iff K H N h hNK x.1).mp x.2)

/-- The restricted coefficient map retains each underlying fixed vector. -/
noncomputable def imageCoefficient (A : Rep.{u} k G) (K H N : Subgroup G)
    [N.Normal] (h : K ≤ H) (hNK : N ≤ K) :
    Rep.res (imageMap K H N h hNK)
        (Rep.res ((K.map (QuotientGroup.mk' N)).subgroupOf
          (H.map (QuotientGroup.mk' N))).subtype
          (Rep.res (H.map (QuotientGroup.mk' N)).subtype (A.quotientToInvariants N))) ⟶
      Rep.res ((K.subgroupOf H).map (QuotientGroup.mk' (N.comap H.subtype))).subtype
        ((Rep.res H.subtype A).quotientToInvariants (N.comap H.subtype)) :=
  Rep.ofHom
    { toLinearMap := (fixedRestrictionEquiv A H N (hNK.trans h)).toLinearMap
      isIntertwining' x := (quotientRestrictionIso A H N (hNK.trans h)).hom.hom.isIntertwining' x.1 }

/-- Covariance transports the inner ordinary transfer to its ambient quotient coordinates. -/
theorem transfer_square (A : Rep.{u} k G) (K H N : Subgroup G) [N.Normal]
    (h : K ≤ H) (hNK : N ≤ K)
    [Fintype ((H.map (QuotientGroup.mk' N)) ⧸
      (K.map (QuotientGroup.mk' N)).subgroupOf (H.map (QuotientGroup.mk' N)))]
    [Fintype ((H ⧸ N.comap H.subtype) ⧸
      (K.subgroupOf H).map (QuotientGroup.mk' (N.comap H.subtype)))] (q : ℕ) :
    Tate.ordinaryCohomologyCorestriction
        ((K.map (QuotientGroup.mk' N)).subgroupOf (H.map (QuotientGroup.mk' N)))
        (Rep.res (H.map (QuotientGroup.mk' N)).subtype (A.quotientToInvariants N)) q ≫
      (quotientSubgroupCohomologyIso A H N (hNK.trans h) q).inv =
    groupCohomology.map (imageMap K H N h hNK) (imageCoefficient A K H N h hNK) q ≫
      Tate.ordinaryCohomologyCorestriction
        ((K.subgroupOf H).map (QuotientGroup.mk' (N.comap H.subtype)))
        ((Rep.res H.subtype A).quotientToInvariants (N.comap H.subtype)) q := by
  have hi : (quotientSubgroupCohomologyIso A H N (hNK.trans h) q).inv =
      groupCohomology.map (quotientSubgroupEquiv H N).toMonoidHom
        (quotientRestrictionIso A H N (hNK.trans h)).hom q := by
    unfold quotientSubgroupCohomologyIso
    rw [groupCohomology.mapIso_inv]
    apply groupCohomology.map_congr rfl
    rfl
  rw [hi]
  exact ordinaryCohomologyCorestriction_comp_map
    (quotientSubgroupEquiv H N).toMonoidHom (quotientSubgroupEquiv H N).surjective
    ((K.map (QuotientGroup.mk' N)).subgroupOf (H.map (QuotientGroup.mk' N)))
    ((K.subgroupOf H).map (QuotientGroup.mk' (N.comap H.subtype)))
    (image_mem_iff K H N h hNK) (imageMap K H N h hNK) (fun _ => rfl)
    (Rep.res (H.map (QuotientGroup.mk' N)).subtype (A.quotientToInvariants N))
    ((Rep.res H.subtype A).quotientToInvariants (N.comap H.subtype))
    (quotientRestrictionIso A H N (hNK.trans h)).hom
    (imageCoefficient A K H N h hNK) rfl q

/-- The direct and iterated subgroup quotient coordinates give the same cohomology map. -/
theorem coordinate_square (A : Rep.{u} k G) (K H N : Subgroup G) [N.Normal]
    (h : K ≤ H) (hNK : N ≤ K) (q : ℕ) :
    (quotientSubgroupCohomologyIso A K N hNK q).inv ≫
        groupCohomology.map (towerQuotientHom h N) (towerFixedCoefficient A h N) q =
      groupCohomology.map
          (Subgroup.subgroupOfEquivOfLe (Subgroup.map_mono h)).toMonoidHom
          (Tate.towerCoefficientIso (Subgroup.map_mono h) (A.quotientToInvariants N)).hom q ≫
        groupCohomology.map (imageMap K H N h hNK) (imageCoefficient A K H N h hNK) q ≫
          (quotientSubgroupCohomologyIso (Rep.res H.subtype A) (K.subgroupOf H)
            (N.comap H.subtype) (fun _ hn => hNK hn) q).inv := by
  unfold quotientSubgroupCohomologyIso
  rw [groupCohomology.mapIso_inv, groupCohomology.mapIso_inv,
    ← groupCohomology.map_comp, ← groupCohomology.map_comp, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · ext x
    rfl
  · rfl

end FiniteTower

set_option backward.isDefEq.respectTransparency false in
/-- Finite corestriction is transitive with the published explicit tower coordinates. -/
theorem finiteCorestrictionTower : FiniteCorestrictionTower.{u} := by
  intro k G _ _ _ _ _ _ A K H h N hNK q
  let : IsTopologicalGroup H := inferInstanceAs (IsTopologicalGroup H.toSubgroup)
  let : CompactSpace H := isCompact_iff_compactSpace.mp H.isClosed.isCompact
  let Kbar := K.toSubgroup.map (QuotientGroup.mk' N.toSubgroup)
  let Hbar := H.toSubgroup.map (QuotientGroup.mk' N.toSubgroup)
  let J := (K.toSubgroup.subgroupOf H.toSubgroup).map
    (QuotientGroup.mk' (N.toSubgroup.comap H.toSubgroup.subtype))
  let Aq := A.toRep.quotientToInvariants N.toSubgroup
  have hbar : Kbar ≤ Hbar := Subgroup.map_mono h
  have : Finite (G ⧸ N.toSubgroup) := finite_quotient N
  have : Finite (H ⧸ N.toSubgroup.comap H.toSubgroup.subtype) :=
    finite_quotient (restrictOpenNormal H N)
  let : Fintype (G ⧸ N.toSubgroup) := Fintype.ofFinite _
  let : Fintype Kbar := Fintype.ofFinite _
  let : Fintype Hbar := Fintype.ofFinite _
  let : Fintype (Kbar.subgroupOf Hbar) := Fintype.ofFinite _
  let : Fintype ((G ⧸ N.toSubgroup) ⧸ Kbar) := Fintype.ofFinite _
  let : Fintype ((G ⧸ N.toSubgroup) ⧸ Hbar) := Fintype.ofFinite _
  let : Fintype (Hbar ⧸ Kbar.subgroupOf Hbar) := Fintype.ofFinite _
  let : Fintype ((H ⧸ N.toSubgroup.comap H.toSubgroup.subtype) ⧸ J) :=
    Fintype.ofFinite _
  have hc := FiniteTower.coordinate_square A.toRep K.toSubgroup H.toSubgroup
    N.toSubgroup h hNK q
  have ht := FiniteTower.transfer_square A.toRep K.toSubgroup H.toSubgroup
    N.toSubgroup h hNK q
  have hcoord :
      (quotientSubgroupCohomologyIso A.toRep K.toSubgroup N.toSubgroup hNK q).hom ≫
        groupCohomology.map (Subgroup.subgroupOfEquivOfLe hbar).toMonoidHom
          (Tate.towerCoefficientIso hbar Aq).hom q ≫
        groupCohomology.map (FiniteTower.imageMap K.toSubgroup H.toSubgroup N.toSubgroup h hNK)
          (FiniteTower.imageCoefficient A.toRep K.toSubgroup H.toSubgroup N.toSubgroup h hNK) q =
      finiteTowerCohomology A h N q ≫
        (quotientSubgroupCohomologyIso (Rep.res H.toSubgroup.subtype A.toRep)
          (K.toSubgroup.subgroupOf H.toSubgroup) (N.toSubgroup.comap H.toSubgroup.subtype)
          (fun _ hn => hNK hn) q).hom := by
    apply (cancel_epi
      (quotientSubgroupCohomologyIso A.toRep K.toSubgroup N.toSubgroup hNK q).inv).mp
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    change _ = ((quotientSubgroupCohomologyIso A.toRep K.toSubgroup N.toSubgroup hNK q).inv ≫
      groupCohomology.map (towerQuotientHom h N.toSubgroup)
        (towerFixedCoefficient A.toRep h N.toSubgroup) q) ≫ _
    rw [hc]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  have htransfer :
      Tate.ordinaryCohomologyCorestriction (Kbar.subgroupOf Hbar)
          (Rep.res Hbar.subtype Aq) q =
        groupCohomology.map (FiniteTower.imageMap K.toSubgroup H.toSubgroup N.toSubgroup h hNK)
          (FiniteTower.imageCoefficient A.toRep K.toSubgroup H.toSubgroup N.toSubgroup h hNK) q ≫
          Tate.ordinaryCohomologyCorestriction J
            ((Rep.res H.toSubgroup.subtype A.toRep).quotientToInvariants
              (N.toSubgroup.comap H.toSubgroup.subtype)) q ≫
            (quotientSubgroupCohomologyIso A.toRep H.toSubgroup N.toSubgroup
              (hNK.trans h) q).hom := by
    apply (cancel_mono
      (quotientSubgroupCohomologyIso A.toRep H.toSubgroup N.toSubgroup (hNK.trans h) q).inv).mp
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using ht
  unfold finiteCorestriction quotientCorestriction
  rw [ordinaryTransferLaws.2 k (G ⧸ N.toSubgroup) Kbar Hbar hbar Aq q,
    htransfer]
  simp only [← Category.assoc]
  rw [show ((quotientSubgroupCohomologyIso A.toRep K.toSubgroup N.toSubgroup hNK q).hom ≫
      groupCohomology.map (Subgroup.subgroupOfEquivOfLe hbar).toMonoidHom
        (Tate.towerCoefficientIso hbar Aq).hom q) ≫
      groupCohomology.map (FiniteTower.imageMap K.toSubgroup H.toSubgroup N.toSubgroup h hNK)
        (FiniteTower.imageCoefficient A.toRep K.toSubgroup H.toSubgroup N.toSubgroup h hNK) q = _
    from (Category.assoc _ _ _).trans hcoord]
  rfl

example : FiniteCorestrictionTower.{u} := finiteCorestrictionTower.{u}

end Langlands.Continuous
