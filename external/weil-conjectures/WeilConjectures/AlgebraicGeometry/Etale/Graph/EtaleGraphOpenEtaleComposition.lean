/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Graph.EtaleGraphChosenComparisons
import WeilConjectures.AlgebraicGeometry.Etale.Graph.EtaleGraphOpenModelComparison
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenSumDerivedAdjunction
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleNormalizedMatesCompositionPasting

/-! # Graph composition with an open first leg

Source: Stacks Project, Tags 0F7I and 0F7J.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local instance 2000] Abelian.toPreadditive

attribute [local irreducible] lowerStar upperStar
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  canonicalEtaleCompactSupportComparison derivedEtaleLowerShriekUpperStarAdjunction
  derivedOpenImmersionLowerShriekUpperStarAdjunction mapDerivedUpperStarLowerStarAdjunction
  rightDerivedLowerShriekIso unboundedEtaleLowerShriekCompIso unboundedEtaleLowerShriekCongr

private theorem graph_chosen_open_eq_etale
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j] [HasCompactification j] :
    graphChosenEtaleComparison A j = graphChosenOpenComparison A j := by
  let c := HasCompactification.compactification j
  let d := Compactification.ofIsOpenImmersion j
  have hc : rightDerivedLowerShriekIso A (HasCompactification.compactification j) =
      Iso.refl _ := by
    unfold rightDerivedLowerShriekIso
    exact (unboundedEtaleCompactSupport_comparison_coherence A j).1 c
  have hd : (rightDerivedLowerShriekIso A d).hom ≫
      (canonicalEtaleCompactSupportComparison A j c).hom =
        (canonicalEtaleCompactSupportComparison A j d).hom := by
    simpa only [rightDerivedLowerShriekIso, c] using
      EtaleSupportExchange.comparison_refinement A j d c
  unfold graphChosenEtaleComparison graphChosenOpenComparison
  dsimp only [rightDerivedLowerShriek, Compactification.ofIsOpenImmersion]
  rw [hc]
  simp only [Iso.refl_symm]
  erw [Iso.refl_trans]
  erw [← etaleGraphOpenModelComparison A j]
  apply Iso.ext
  apply (cancel_epi (rightDerivedLowerShriekIso A d).hom).1
  simp only [Iso.trans_hom, Iso.symm_hom]
  change (rightDerivedLowerShriekIso A d).hom ≫
      (canonicalEtaleCompactSupportComparison A j c).hom =
    (rightDerivedLowerShriekIso A d).hom ≫ (rightDerivedLowerShriekIso A d).inv ≫
      (canonicalEtaleCompactSupportComparison A j d).hom
  rw [Iso.hom_inv_id_assoc]
  exact hd

/-- Graph extension for an open immersion followed by an etale map agrees with
composition of their left adjoints. There is no proper square in this assertion.
Source: Stacks Project, etale-cohomology.tex Tag 0F4L, and more-etale.tex Tag 0F7J
(blueprint: lem-pur-graph-open-etale-composition).

Proof in words: choose a compactification of b and compactify j over its open part.
Expand the compact-support compositor in this tower. A lift section on the open source
extends by zero onto exactly its clopen graph, whether one first applies j or first uses
the graph comparison for b. On the complement both sections are zero; on the graph they
are the original section. The sheaf axiom and sum-presheaf sheafification identify the
maps. The transpose under the composite sum/open adjunction is the inverse-image
compositor for r = j followed by b, so its conjugate is precisely s. Apply the equality
degreewise, compose with the right-derived units, and use their composition equation.
Homotopy localization and graph refinement coherence remove the auxiliary tower and
prove the equation for the chosen comparisons. Identity and empty opens are included. -/
theorem graph_open_etale_composition
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X W Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian W] [IsNoetherian Z]
    (j : X ⟶ W) [IsOpenImmersion j] [QuasiCompact j]
    (b : W ⟶ Z) [Etale b] [IsSeparated b] [QuasiCompact b]
    (r : X ⟶ Z) [Etale r] [IsSeparated r] [QuasiCompact r]
    (hr : r = j ≫ b)
    [HasCompactification j] [HasCompactification b] [HasCompactification r]
    [HasCompactification (j ≫ b)] (e : Compactification r) :
    let s := (conjugateIsoEquiv
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) r inferInstance)
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).comp
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) b inferInstance))).symm
      (Functor.mapDerivedCategoryNatIso
        (upperStarComp (ModuleCat.{u + 1} A) j b r hr) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm)
    Functor.isoWhiskerRight (graphChosenOpenComparison A j)
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) b) ≪≫
      Functor.isoWhiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory
        (graphChosenEtaleComparison A b) ≪≫ s =
      unboundedEtaleLowerShriekCompIso A j b ≪≫
        unboundedEtaleLowerShriekCongr A hr.symm ≪≫
        (rightDerivedLowerShriekIso A e).symm ≪≫
        canonicalEtaleCompactSupportComparison A r e := by
  subst r
  dsimp only
  have hs : (conjugateIsoEquiv
      (derivedEtaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) (j ≫ b) inferInstance)
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j).comp
        (derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) b inferInstance))).symm
        (Functor.mapDerivedCategoryNatIso
          (upperStarComp (ModuleCat.{u + 1} A) j b (j ≫ b) rfl) ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm) = derivedEtaleSumCompIso A j b := by
    rw [etaleOpenSumDerivedAdjunction]
    apply (conjugateIsoEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    apply Iso.ext
    exact (etaleSumCompositionCounit A j b).2.symm
  rw [hs, ← graph_chosen_open_eq_etale A j]
  change Functor.isoWhiskerRight (graphChosenEtaleComparison A j)
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) b) ≪≫
      Functor.isoWhiskerLeft
        (etaleLowerShriek (ModuleCat.{u + 1} A) j inferInstance).mapDerivedCategory
        (graphChosenEtaleComparison A b) ≪≫ derivedEtaleSumCompIso A j b =
      unboundedEtaleLowerShriekCompIso A j b ≪≫
        unboundedEtaleLowerShriekCongr A rfl ≪≫
        (rightDerivedLowerShriekIso A e).symm ≪≫
        canonicalEtaleCompactSupportComparison A (j ≫ b) e
  let c := HasCompactification.compactification j
  let d := HasCompactification.compactification b
  have hc : rightDerivedLowerShriekIso A (HasCompactification.compactification j) =
      Iso.refl _ := by
    unfold rightDerivedLowerShriekIso
    exact (unboundedEtaleCompactSupport_comparison_coherence A j).1 c
  have hd : rightDerivedLowerShriekIso A (HasCompactification.compactification b) =
      Iso.refl _ := by
    unfold rightDerivedLowerShriekIso
    exact (unboundedEtaleCompactSupport_comparison_coherence A b).1 d
  apply Iso.ext
  apply NatTrans.ext
  funext M
  have ht := support_compositor_global A j b c d e M
  dsimp only [c, d] at ht
  simp only [hc, hd, Iso.refl_hom, NatTrans.id_app, Category.id_comp] at ht
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at ht
  have hsum := congr_app (etaleSupportSumCompositor A j b c d e) M
  have htransport := congrArg (fun z ↦ z ≫ (rightDerivedLowerShriekIso A e).inv.app M ≫
    (canonicalEtaleCompactSupportComparison A (j ≫ b) e).hom.app M) ht
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc] at htransport
  unfold graphChosenEtaleComparison
  dsimp only [rightDerivedLowerShriek]
  simp only [hc, hd, Iso.refl_symm, Iso.refl_trans,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    unboundedEtaleLowerShriekCongr, Iso.refl_hom, NatTrans.id_app]
  erw [Category.id_comp]
  change _ = (unboundedEtaleLowerShriekCompIso A j b).hom.app M ≫
    (rightDerivedLowerShriekIso A e).inv.app M ≫
      (canonicalEtaleCompactSupportComparison A (j ≫ b) e).hom.app M
  rw [(canonicalEtaleCompactSupportComparison A b d).hom.naturality_assoc]
  apply Eq.trans _ htransport
  simpa only [etaleNormalizedSupportCompositor, NatTrans.comp_app, NatTrans.hcomp_app,
    Category.assoc] using hsum.symm

end AlgebraicGeometry.Etale
