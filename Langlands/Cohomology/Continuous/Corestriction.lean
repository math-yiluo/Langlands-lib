import Langlands.Cohomology.Continuous.TransferSource
import Langlands.Cohomology.Continuous.FiniteCorestrictionRefinementProof

universe u

open CategoryTheory

namespace Langlands.Continuous

variable {k G : Type u} [CommRing k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

set_option backward.isDefEq.respectTransparency false in
/-- The finite transfers, followed by genuine continuous inflation, form the transfer cocone. -/
noncomputable def continuousCorestrictionCocone (A : DiscreteModule k G)
    (H : OpenSubgroup G) (q : ℕ) : Limits.Cocone (transferSourceDiagram A.toRep H q) where
  pt := (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).obj
    (continuousCohomology q A.toTopRep)
  ι :=
    { app := fun N =>
        finiteCorestriction A.toRep H (ambientOpenNormalCore H ⊓ OrderDual.ofDual N)
            (fun _ hx => ambientOpenNormalCore_le H hx.1) q ≫
          finiteStageToContinuous A (ambientOpenNormalCore H ⊓ OrderDual.ofDual N) q
      naturality := fun N M f => by
        let hMN : ambientOpenNormalCore H ⊓ OrderDual.ofDual M ≤
            ambientOpenNormalCore H ⊓ OrderDual.ofDual N :=
          inf_le_inf_left _ (leOfHom (X := FiniteQuotientIndex (G := G)) f)
        change finiteInflation (Rep.res H.toSubgroup.subtype A.toRep) q
            (restrictOpenNormal_le H hMN) ≫
            (finiteCorestriction A.toRep H (ambientOpenNormalCore H ⊓ OrderDual.ofDual M)
                (fun _ hx => ambientOpenNormalCore_le H hx.1) q ≫
              finiteStageToContinuous A (ambientOpenNormalCore H ⊓ OrderDual.ofDual M) q) = _
        rw [← Category.assoc, finiteCorestrictionRefinement k G A.toRep H _ _ hMN
          (fun _ hx => ambientOpenNormalCore_le H hx.1) q, Category.assoc,
          finiteStageToContinuous_refinement]
        exact (Category.comp_id _).symm }

/-- Corestriction on the actual underlying continuous cohomology modules. -/
noncomputable def continuousCorestriction (A : DiscreteModule k G)
    (H : OpenSubgroup G) (q : ℕ) :
    (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).obj
        (continuousCohomology q (A.restrict H.toSubgroup).toTopRep) ⟶
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).obj
        (continuousCohomology q A.toTopRep) :=
  (transferSourceComparisonIso A H q).inv ≫
    Limits.colimit.desc _ (continuousCorestrictionCocone A H q)

set_option backward.isDefEq.respectTransparency false in
theorem continuousCorestriction_core_stage (A : DiscreteModule k G)
    (H : OpenSubgroup G) (N : OpenNormalSubgroup G) (q : ℕ) :
    finiteStageToContinuous (A.restrict H.toSubgroup)
        (restrictOpenNormal H (ambientOpenNormalCore H ⊓ N)) q ≫
      continuousCorestriction A H q =
    finiteCorestriction A.toRep H (ambientOpenNormalCore H ⊓ N)
        (fun _ hx => ambientOpenNormalCore_le H hx.1) q ≫
      finiteStageToContinuous A (ambientOpenNormalCore H ⊓ N) q := by
  unfold continuousCorestriction
  rw [← Category.assoc, transferSourceComparisonIso_inv_ι, Limits.colimit.ι_desc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Corestriction agrees with the actual finite transfer at every normal stage inside H. -/
theorem finiteStageToContinuous_comp_corestriction (A : DiscreteModule k G)
    (H : OpenSubgroup G) (N : OpenNormalSubgroup G)
    (hNH : N.toSubgroup ≤ H.toSubgroup) (q : ℕ) :
    finiteStageToContinuous (A.restrict H.toSubgroup) (restrictOpenNormal H N) q ≫
      continuousCorestriction A H q =
    finiteCorestriction A.toRep H N hNH q ≫ finiteStageToContinuous A N q := by
  have hCN : ambientOpenNormalCore H ⊓ N ≤ N := inf_le_right
  rw [← finiteStageToContinuous_refinement (A.restrict H.toSubgroup)
    (restrictOpenNormal_le H hCN) q, Category.assoc,
    continuousCorestriction_core_stage, ← Category.assoc]
  exact (congrArg (fun f => f ≫
      finiteStageToContinuous A (ambientOpenNormalCore H ⊓ N) q)
    (finiteCorestrictionRefinement k G A.toRep H _ N hCN hNH q)).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun f => finiteCorestriction A.toRep H N hNH q ≫ f)
          (finiteStageToContinuous_refinement A hCN q)))

end Langlands.Continuous
