/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Graph.EtaleGraphChosenComparisons
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

/-! # The open/proper model of the compact-support compositor

Source: Stacks Project, Tags 0F7I and 0F7J.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  canonicalEtaleCompactSupportComparison derivedEtaleLowerShriekUpperStarAdjunction
  derivedOpenImmersionLowerShriekUpperStarAdjunction mapDerivedUpperStarLowerStarAdjunction
  rightDerivedLowerShriekIso unboundedEtaleLowerShriekCompIso unboundedEtaleLowerShriekCongr
  rightDerivedLowerStarIdIso Functor.mapDerivedCategoryNatIso

-- Reduce only the small structural records while matching their identity-map instances.
set_option allowUnsafeReducibility true in
attribute [local reducible] unboundedFormalism ExchangeFormalism.shriek
  Compactification.ofIsProper Compactification.ofIsOpenImmersion Compactification.copy
  Compactification.postcomp rightDerivedLowerStar rightDerivedLowerShriek

attribute [local instance] unbounded_has_base_change unbounded_has_proper_exchange

@[reducible] private noncomputable def factorTriangle
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Compactification.Triangle c.i c.g where
  cf := Compactification.ofIsOpenImmersion c.i
  cg := Compactification.ofIsProper c.g
  cfg := c.copy c.comm.symm
  q := 𝟙 c.Z
  p := 𝟙 c.Z
  isOpenImmersion_q := by
    change IsOpenImmersion (𝟙 c.Z)
    infer_instance
  i_q := Category.comp_id _
  p_g := Category.id_comp _
  isPullback := by
    change IsPullback (𝟙 c.Z) (𝟙 c.Z) (𝟙 c.Z) (𝟙 c.Z)
    exact IsPullback.of_vert_isIso ⟨rfl⟩

private lemma model_factorization
    (F : CompactSupportFormalism.{_, _, u}) [F.HasProperExchange]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (K : F.obj X) :
    (F.compIso (factorTriangle c)).hom.app K =
      (F.pf c.g).map
        ((F.shId c.Z).hom.app ((F.pf (𝟙 c.Z)).obj ((F.sh c.i).obj K)) ≫
          (F.pfId c.Z).hom.app ((F.sh c.i).obj K)) := by
  let T := factorTriangle c
  have hw : (𝟙 c.Z) ≫ (𝟙 c.Z) = (𝟙 c.Z) ≫ (𝟙 c.Z) := by simp
  have : IsIso (F.baseChange (𝟙 c.Z) (𝟙 c.Z) (𝟙 _) (𝟙 c.Z) hw) :=
    CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) (IsPullback.of_vert_isIso ⟨hw⟩)
  have h₁ := congr_app (F.exchange_id_vert (𝟙 c.Z) hw) ((F.sh c.i).obj K)
  have h₂ := congr_app (F.shComp'_id_right c.i) K
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_hom_app, Category.comp_id, Functor.comp_obj, Functor.id_obj]
    at h₁ h₂
  have hSC : (F.shComp' c.i (𝟙 c.Z) c.i (Category.comp_id _)).inv.app K =
      (F.shId c.Z).hom.app ((F.sh c.i).obj K) := by
    rw [← cancel_epi ((F.shComp' c.i (𝟙 c.Z) c.i (Category.comp_id _)).hom.app K),
      Iso.hom_inv_id_app]
    exact h₂.symm
  rw [F.compIso_hom_app]
  dsimp +instances only [factorTriangle, Compactification.ofIsProper,
    Compactification.ofIsOpenImmersion, Compactification.copy]
  rw [h₁, hSC, F.pfComp'_id_left_inv_app]
  simp [← Functor.map_comp]

private lemma chosen_to_model
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [(unboundedFormalism A).HasProperExchange]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    [HasCompactification f] (c : Compactification f) :
    (unboundedFormalism A).shriekIso (HasCompactification.compactification f) c =
      (rightDerivedLowerShriekIso A c).symm := by
  rw [← (unboundedFormalism A).shriekIso_symm c
    (HasCompactification.compactification f), unbounded_shriek_iso]
  unfold rightDerivedLowerShriekIso
  rfl

/-- Factorization normalization of the chosen compositor.
Source: Stacks Project, Tags 0F7I and 0F7J
(blueprint: lem-pur-graph-compactification-factorization).

Proof in words: use the triangle whose three compactifications are the identity-proper
compactification of the open leg, the identity-open compactification of the proper leg,
and c. Its middle square is the identity square on c.Z. The every-triangle composition
formula reduces its interchange to the identity. Remove the identity open and proper
functors using their adjunction unit normalizations. The common-refinement cocycle
identifies the three remaining comparisons with the chosen ones. This proves the displayed
identity, including when c.i is empty or an identity. -/
theorem graph_compactification_factorization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] (c : Compactification f)
    [QuasiCompact c.i] [HasCompactification c.i] [HasCompactification (c.i ≫ c.g)] :
    Functor.isoWhiskerRight (graphChosenOpenComparison A c.i)
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) c.g) ≪≫
      Functor.isoWhiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
        (graphChosenProperComparison A c.g) ≪≫ rightDerivedLowerShriekIso A c =
      unboundedEtaleLowerShriekCompIso A c.i c.g ≪≫
        unboundedEtaleLowerShriekCongr A c.comm.symm := by
  rcases c with ⟨W, q, j, hcomm, hq, hj⟩
  subst f
  let := hq
  let := hj
  let c : Compactification (j ≫ q) := ⟨W, q, j, rfl, hq, hj⟩
  let F := unboundedFormalism A
  let : F.HasProperExchange := unbounded_has_proper_exchange A
  let T := factorTriangle c
  have h := F.lowerShriekCompIso_hom_eq T
  rw [unbounded_chosen_comp] at h
  simp only [F, chosen_to_model, Iso.symm_hom] at h
  rw [unbounded_shriek_iso] at h
  apply Iso.ext
  apply NatTrans.ext
  funext K
  simp only [unboundedEtaleLowerShriekCongr, Iso.trans_refl]
  change _ = (unboundedEtaleLowerShriekCompIso A j q).hom.app K
  rw [congr_app h K]
  rw [NatTrans.comp_app, NatTrans.comp_app, model_factorization]
  dsimp +instances only [T, factorTriangle, Compactification.copy, c]
  rw [unbounded_pf_id, unbounded_sh_id]
  simp only [graphChosenOpenComparison, graphChosenProperComparison,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, NatTrans.hcomp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_hom_app, Functor.map_comp, Category.assoc]
  erw [(rightDerivedLowerShriekIso A (Compactification.ofIsProper q)).inv.naturality_assoc]
  erw [(rightDerivedLowerShriekIso A (Compactification.ofIsProper q)).inv.naturality_assoc]
  erw [(rightDerivedLowerShriekIso A (Compactification.ofIsProper q)).inv.naturality_assoc]
  let z := Functor.mapDerivedCategoryNatIso
    (Adjunction.leftAdjointIdIso
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 W))
      (upperStarId (ModuleCat.{u + 1} A) W)) ≪≫ Functor.mapDerivedCategoryIdIso _
  have hn := z.hom.naturality ((rightDerivedLowerStarIdIso A W).hom.app
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K))
  dsimp only [Functor.id_map] at hn
  have hh := congrArg (fun a ↦
    (rightDerivedLowerShriekIso A (Compactification.ofIsProper q)).inv.app
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) j).obj K) ≫
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) q).map
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) (𝟙 W)).mapDerivedCategory.map
        ((rightDerivedLowerShriekIso A (Compactification.ofIsOpenImmersion j)).inv.app K)) ≫
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) q).map a ≫
      (rightDerivedLowerShriekIso A c).hom.app K) hn
  conv_lhs =>
    enter [2, 2, 2]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    erw [Category.id_comp]
  simpa only [z, c, rightDerivedLowerStarIdIso, rightDerivedLowerShriekIso,
    Iso.trans_hom, NatTrans.comp_app, Functor.comp_map, Functor.map_comp,
    CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id, Functor.id_obj, Category.assoc] using hh

end AlgebraicGeometry.Etale
