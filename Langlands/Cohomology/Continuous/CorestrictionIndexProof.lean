import Langlands.Cohomology.Continuous.Corestriction
import Langlands.Cohomology.Continuous.OrdinaryTransferLawsProof
import Langlands.Cohomology.Continuous.CorestrictionLawsStatement
import Langlands.Cohomology.Continuous.RestrictionComparisonProof

universe u

open CategoryTheory

namespace Langlands.Continuous

variable {k G : Type u} [CommRing k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

set_option backward.isDefEq.respectTransparency false in
theorem finiteRestriction_corestriction_index (A : DiscreteModule k G)
    (H : OpenSubgroup G) (N : OpenNormalSubgroup G)
    (hNH : N.toSubgroup ≤ H.toSubgroup) (q : ℕ) :
    finiteRestriction A H N q ≫ finiteCorestriction A.toRep H N hNH q =
      H.toSubgroup.index • 𝟙 (groupCohomology (finiteQuotientRep A.toRep N) q) := by
  let : Finite (G ⧸ N.toSubgroup) := finite_quotient N
  let := Fintype.ofFinite (G ⧸ N.toSubgroup)
  let := Fintype.ofFinite (H.toSubgroup.map (QuotientGroup.mk' N.toSubgroup))
  let := Fintype.ofFinite
    ((G ⧸ N.toSubgroup) ⧸ H.toSubgroup.map (QuotientGroup.mk' N.toSubgroup))
  unfold finiteCorestriction quotientCorestriction
  rw [← Category.assoc, finiteRestriction_quotientSubgroupCohomologyIso]
  have hindex : (H.toSubgroup.map (QuotientGroup.mk' N.toSubgroup)).index =
      H.toSubgroup.index :=
    H.toSubgroup.index_map_eq (QuotientGroup.mk'_surjective N.toSubgroup)
      (by simpa only [QuotientGroup.ker_mk'] using hNH)
  have ordinaryIndex : OrdinaryCorestrictionIndex.{u} := ordinaryTransferLaws.1
  rw [ordinaryIndex, hindex]

set_option backward.isDefEq.respectTransparency false in
theorem continuousRestriction_corestriction_index (A : DiscreteModule k G)
    (H : OpenSubgroup G) (q : ℕ) :
    (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
        (continuousRestriction A H.toSubgroup q) ≫
      continuousCorestriction A H q =
    H.toSubgroup.index • 𝟙 ((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).obj
      (continuousCohomology q A.toTopRep)) := by
  have stage (N : OpenNormalSubgroup G) (hNH : N.toSubgroup ≤ H.toSubgroup) :
      finiteStageToContinuous A N q ≫
          ((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
              (continuousRestriction A H.toSubgroup q) ≫
            continuousCorestriction A H q) =
        finiteStageToContinuous A N q ≫
          (H.toSubgroup.index • 𝟙 ((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).obj
            (continuousCohomology q A.toTopRep))) := by
    rw [← Category.assoc, ← finiteRestriction_comp_stage, Category.assoc,
      finiteStageToContinuous_comp_corestriction A H N hNH q,
      ← Category.assoc, finiteRestriction_corestriction_index,
      Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]
  apply (cancel_epi (finiteQuotientComparison A q)).mp
  apply Limits.colimit.hom_ext
  intro N
  change finiteStageToColimit A.toRep (OrderDual.ofDual N) q ≫ _ =
    finiteStageToColimit A.toRep (OrderDual.ofDual N) q ≫ _
  simp only [← Category.assoc, finiteStageToColimit_comp_comparison]
  have h := congrArg (fun f => finiteInflation A.toRep q
      (show ambientOpenNormalCore H ⊓ OrderDual.ofDual N ≤ OrderDual.ofDual N from
        inf_le_right) ≫ f)
    (stage (ambientOpenNormalCore H ⊓ OrderDual.ofDual N)
      (fun _ hx => ambientOpenNormalCore_le H hx.1))
  simpa only [← Category.assoc, finiteStageToContinuous_refinement] using h

/-- The exact index identity on actual continuous cohomology. -/
theorem continuousCorestrictionIndex : ContinuousCorestrictionIndex.{u} := by
  intro k G _ _ _ _ _ _ A H q
  exact continuousRestriction_corestriction_index A H q

end Langlands.Continuous
