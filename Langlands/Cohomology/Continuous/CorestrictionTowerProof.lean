import Langlands.Cohomology.Continuous.Corestriction
import Langlands.Cohomology.Continuous.CorestrictionLawsStatement
import Langlands.Cohomology.Continuous.FiniteCorestrictionTowerProof

universe u

open CategoryTheory

namespace Langlands.Continuous

variable {k G : Type u} [CommRing k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

set_option backward.isDefEq.respectTransparency false in
theorem continuousCorestriction_tower (A : DiscreteModule k G)
    (K H : OpenSubgroup G) (h : K.toSubgroup ≤ H.toSubgroup) (q : ℕ) :
    let : CompactSpace H := isCompact_iff_compactSpace.mp H.isClosed.isCompact
    continuousCorestriction A K q =
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
          (continuousTowerCohomologyIso A h q).hom ≫
        continuousCorestriction (A.restrict H.toSubgroup) (towerOpenSubgroup K H) q ≫
        continuousCorestriction A H q := by
  let : CompactSpace H := isCompact_iff_compactSpace.mp H.isClosed.isCompact
  have stage (N : OpenNormalSubgroup G) (hNK : N.toSubgroup ≤ K.toSubgroup) :
      finiteStageToContinuous (A.restrict K.toSubgroup) (restrictOpenNormal K N) q ≫
          continuousCorestriction A K q =
        finiteStageToContinuous (A.restrict K.toSubgroup) (restrictOpenNormal K N) q ≫
          ((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
              (continuousTowerCohomologyIso A h q).hom ≫
            continuousCorestriction (A.restrict H.toSubgroup) (towerOpenSubgroup K H) q ≫
            continuousCorestriction A H q) := by
    have hnested := finiteStageToContinuous_comp_corestriction
      (A.restrict H.toSubgroup) (towerOpenSubgroup K H) (restrictOpenNormal H N)
      (fun _ hn => hNK hn) q
    have hambient := finiteStageToContinuous_comp_corestriction
      A H N (fun _ hn => h (hNK hn)) q
    have htower := finiteTowerCohomology_comp_stage A h N q
    rw [finiteStageToContinuous_comp_corestriction A K N hNK q,
      finiteCorestrictionTower k G A K H h N hNK q]
    have hstep := congrArg (fun t => finiteTowerCohomology A h N q ≫
        (t ≫ continuousCorestriction A H q)) hnested
    have hstep2 := congrArg (fun t => finiteTowerCohomology A h N q ≫
        (finiteCorestriction (A.restrict H.toSubgroup).toRep
          (towerOpenSubgroup K H) (restrictOpenNormal H N) (fun _ hn => hNK hn) q ≫ t))
      hambient
    have hstep3 := congrArg (fun t => t ≫
        continuousCorestriction (A.restrict H.toSubgroup) (towerOpenSubgroup K H) q ≫
        continuousCorestriction A H q) htower
    simp only [Category.assoc] at hstep hstep2 hstep3 ⊢
    exact hstep2.symm.trans (hstep.symm.trans hstep3)
  apply (cancel_epi (transferSourceComparisonIso A K q).hom).mp
  apply Limits.colimit.hom_ext
  intro N
  change (Limits.colimit.ι (transferSourceDiagram A.toRep K q)
      (OrderDual.toDual (OrderDual.ofDual N))) ≫ _ =
    (Limits.colimit.ι (transferSourceDiagram A.toRep K q)
      (OrderDual.toDual (OrderDual.ofDual N))) ≫ _
  simp only [← Category.assoc, transferSourceComparisonIso_ι]
  exact (stage (ambientOpenNormalCore K ⊓ OrderDual.ofDual N)
    (fun _ hn => ambientOpenNormalCore_le K hn.1)).trans (by simp only [Category.assoc])

/-- The exact tower identity on actual continuous cohomology. -/
theorem continuousCorestrictionTower : ContinuousCorestrictionTower.{u} := by
  intro k G _ _ _ _ _ _ A K H h q
  exact continuousCorestriction_tower A K H h q

end Langlands.Continuous
