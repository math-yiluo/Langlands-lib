import Langlands.Cohomology.Continuous.CorestrictionLawsStatement
import Langlands.Cohomology.Continuous.CoefficientComparisonProof
import Langlands.Cohomology.Tate.CohomologyTransferNaturality

universe u

open CategoryTheory

set_option maxHeartbeats 400000

namespace Langlands.Continuous

variable {k G : Type u} [CommRing k] [Group G]

set_option backward.isDefEq.respectTransparency false in
theorem quotientSubgroupCohomologyIso_naturality {A B : Rep.{u} k G}
    (f : A ⟶ B) (H N : Subgroup G) [N.Normal] (hNH : N ≤ H) (q : ℕ) :
    groupCohomology.map (MonoidHom.id (H ⧸ N.comap H.subtype))
        ((Rep.quotientToInvariantsFunctor k (N.comap H.subtype)).map
          ((Rep.resFunctor H.subtype).map f)) q ≫
        (quotientSubgroupCohomologyIso B H N hNH q).hom =
      (quotientSubgroupCohomologyIso A H N hNH q).hom ≫
        groupCohomology.map (MonoidHom.id (H.map (QuotientGroup.mk' N)))
          ((Rep.resFunctor (H.map (QuotientGroup.mk' N)).subtype).map
            ((Rep.quotientToInvariantsFunctor k N).map f)) q := by
  unfold quotientSubgroupCohomologyIso
  rw [groupCohomology.mapIso_hom, groupCohomology.mapIso_hom,
    ← groupCohomology.map_comp, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · rfl
  · rfl

set_option backward.isDefEq.respectTransparency false in
theorem quotientCorestriction_naturality {A B : Rep.{u} k G} (f : A ⟶ B)
    (H N : Subgroup G) [N.Normal] [Fintype ((G ⧸ N) ⧸ H.map (QuotientGroup.mk' N))]
    (hNH : N ≤ H) (q : ℕ) :
    groupCohomology.map (MonoidHom.id (H ⧸ N.comap H.subtype))
        ((Rep.quotientToInvariantsFunctor k (N.comap H.subtype)).map
          ((Rep.resFunctor H.subtype).map f)) q ≫
        quotientCorestriction B H N hNH q =
      quotientCorestriction A H N hNH q ≫
        groupCohomology.map (MonoidHom.id (G ⧸ N))
          ((Rep.quotientToInvariantsFunctor k N).map f) q := by
  unfold quotientCorestriction
  rw [← Category.assoc, quotientSubgroupCohomologyIso_naturality, Category.assoc]
  exact (congrArg (fun t => (quotientSubgroupCohomologyIso A H N hNH q).hom ≫ t)
    (Langlands.Tate.ordinaryCohomologyCorestriction_naturality (H.map (QuotientGroup.mk' N))
      ((Rep.quotientToInvariantsFunctor k N).map f) q)).trans
        (Category.assoc _ _ _).symm

variable [TopologicalSpace k] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

set_option backward.isDefEq.respectTransparency false in
omit [TopologicalSpace k] [IsTopologicalGroup G] [CompactSpace G] in
theorem finiteCohomologyCoefficient_app {A B : Rep.{u} k G} (f : A ⟶ B)
    (N : OpenNormalSubgroup G) (q : ℕ) :
    (finiteCohomologyCoefficient f q).app (OrderDual.toDual N) =
      groupCohomology.map (MonoidHom.id (G ⧸ N.toSubgroup))
        ((Rep.quotientToInvariantsFunctor k N.toSubgroup).map f) q := rfl

set_option backward.isDefEq.respectTransparency false in
omit [TopologicalSpace k] in
theorem finiteCorestriction_naturality {A B : Rep.{u} k G} (f : A ⟶ B)
    (H : OpenSubgroup G) (N : OpenNormalSubgroup G)
    (hNH : N.toSubgroup ≤ H.toSubgroup) (q : ℕ) :
    (finiteCohomologyCoefficient ((Rep.resFunctor H.toSubgroup.subtype).map f) q).app
        (OrderDual.toDual (restrictOpenNormal H N)) ≫
        finiteCorestriction B H N hNH q =
      finiteCorestriction A H N hNH q ≫
        (finiteCohomologyCoefficient f q).app (OrderDual.toDual N) := by
  let : Finite (G ⧸ N.toSubgroup) := finite_quotient N
  let := Fintype.ofFinite
    ((G ⧸ N.toSubgroup) ⧸ H.toSubgroup.map (QuotientGroup.mk' N.toSubgroup))
  exact quotientCorestriction_naturality f H.toSubgroup N.toSubgroup hNH q


set_option backward.isDefEq.respectTransparency false in
theorem continuousCorestriction_naturality {A B : DiscreteModule k G}
    (f : A.toTopRep ⟶ B.toTopRep) (H : OpenSubgroup G) (q : ℕ) :
    (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
        (ContinuousCohomology.map (ContinuousMonoidHom.id H.toSubgroup)
          ((TopRep.resFunctor H.toSubgroup.subtype).map f) q) ≫
        continuousCorestriction B H q =
      continuousCorestriction A H q ≫
        (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
          (ContinuousCohomology.map (ContinuousMonoidHom.id G) f q) := by
  let fH : (A.restrict H.toSubgroup).toTopRep ⟶ (B.restrict H.toSubgroup).toTopRep :=
    (TopRep.resFunctor H.toSubgroup.subtype).map f
  let fR : A.toRep ⟶ B.toRep := Rep.ofHom f.hom.toIntertwiningMap
  have stage (M : OpenNormalSubgroup G) (hMH : M.toSubgroup ≤ H.toSubgroup) :
      finiteStageToContinuous (A.restrict H.toSubgroup) (restrictOpenNormal H M) q ≫
          ((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
              (ContinuousCohomology.map (ContinuousMonoidHom.id H.toSubgroup) fH q) ≫
            continuousCorestriction B H q) =
        finiteStageToContinuous (A.restrict H.toSubgroup) (restrictOpenNormal H M) q ≫
          (continuousCorestriction A H q ≫
            (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
              (ContinuousCohomology.map (ContinuousMonoidHom.id G) f q)) := by
    have hf := finiteCohomologyCoefficient_comp_stage
      (A := A.restrict H.toSubgroup) (B := B.restrict H.toSubgroup)
      fH (restrictOpenNormal H M) q
    have hn := finiteCorestriction_naturality fR H M hMH q
    calc
      _ = ((finiteCohomologyCoefficient (Rep.ofHom fH.hom.toIntertwiningMap) q).app
            (OrderDual.toDual (restrictOpenNormal H M)) ≫
          finiteStageToContinuous (B.restrict H.toSubgroup) (restrictOpenNormal H M) q) ≫
            continuousCorestriction B H q := by
        exact (Category.assoc _ _ _).symm.trans
          (congrArg (fun t => t ≫ continuousCorestriction B H q) hf.symm)
      _ = (finiteCohomologyCoefficient (Rep.ofHom fH.hom.toIntertwiningMap) q).app
            (OrderDual.toDual (restrictOpenNormal H M)) ≫
          (finiteCorestriction B.toRep H M hMH q ≫ finiteStageToContinuous B M q) := by
        rw [Category.assoc, finiteStageToContinuous_comp_corestriction]
      _ = (finiteCorestriction A.toRep H M hMH q ≫
            (finiteCohomologyCoefficient fR q).app (OrderDual.toDual M)) ≫
          finiteStageToContinuous B M q := by
        exact (Category.assoc _ _ _).symm.trans
          (congrArg (fun t => t ≫ finiteStageToContinuous B M q) hn)
      _ = (finiteCorestriction A.toRep H M hMH q ≫ finiteStageToContinuous A M q) ≫
          (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
            (ContinuousCohomology.map (ContinuousMonoidHom.id G) f q) := by
        rw [Category.assoc, finiteCohomologyCoefficient_comp_stage f, ← Category.assoc]
      _ = _ := by
        rw [← finiteStageToContinuous_comp_corestriction A H M hMH q,
          Category.assoc]
  apply (cancel_epi (transferSourceComparisonIso A H q).hom).mp
  apply Limits.colimit.hom_ext
  intro N
  change (Limits.colimit.ι (transferSourceDiagram A.toRep H q)
      (OrderDual.toDual (OrderDual.ofDual N))) ≫ _ =
    (Limits.colimit.ι (transferSourceDiagram A.toRep H q)
      (OrderDual.toDual (OrderDual.ofDual N))) ≫ _
  simp only [← Category.assoc, transferSourceComparisonIso_ι]
  exact (Category.assoc _ _ _).trans
    ((stage (ambientOpenNormalCore H ⊓ OrderDual.ofDual N)
      (fun _ hx => ambientOpenNormalCore_le H hx.1)).trans
        (Category.assoc _ _ _).symm)

/-- Exact finite-stage compatibility and coefficient naturality of continuous transfer. -/
theorem continuousCorestrictionCompatibility : ContinuousCorestrictionCompatibility.{u} := by
  constructor
  · intro k G _ _ _ _ _ _ A H N hNH q
    exact finiteStageToContinuous_comp_corestriction A H N hNH q
  · intro k G _ _ _ _ _ _ A B f H q
    exact continuousCorestriction_naturality f H q

end Langlands.Continuous
