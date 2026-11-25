/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Graph.EtaleGraphChosenComparisons
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

/-! # Proper postcomposition on compactification models

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

-- Reduce only the small structural records while matching their identity-map instances.
set_option allowUnsafeReducibility true in
attribute [local reducible] unboundedFormalism ExchangeFormalism.shriek
  Compactification.ofIsProper Compactification.ofIsOpenImmersion Compactification.copy
  Compactification.postcomp rightDerivedLowerStar rightDerivedLowerShriek

attribute [local instance] unbounded_has_base_change unbounded_has_proper_exchange

@[reducible] private noncomputable def postTriangle
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (p : Y ⟶ Z) [IsProper p] : Compactification.Triangle f p where
  cf := c
  cg := Compactification.ofIsProper p
  cfg := c.postcomp p
  q := 𝟙 c.Z
  p := c.g
  i_q := Category.comp_id _
  p_g := rfl
  isPullback := by
    change IsPullback c.g (𝟙 c.Z) (𝟙 Y) c.g
    exact IsPullback.of_vert_isIso ⟨by simp⟩

private lemma model_postcomposition
    (F : CompactSupportFormalism.{_, _, u}) [F.HasProperExchange]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (p : Y ⟶ Z) [IsProper p] (K : F.obj X) :
    (F.compIso (postTriangle c p)).hom.app K =
      (F.pf p).map ((F.shId Y).hom.app ((F.pf c.g).obj ((F.sh c.i).obj K))) ≫
        (F.pfComp' c.g p (c.g ≫ p) rfl).inv.app ((F.sh c.i).obj K) := by
  let T := postTriangle c p
  have hw : c.g ≫ 𝟙 Y = 𝟙 c.Z ≫ c.g := by simp
  have : IsIso (F.baseChange c.g (𝟙 c.Z) (𝟙 _) c.g hw) :=
    CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) (IsPullback.of_vert_isIso ⟨hw⟩)
  have h₁ := congr_app (F.exchange_id_vert c.g hw) ((F.sh c.i).obj K)
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
  dsimp +instances only [postTriangle, Compactification.ofIsProper, Compactification.postcomp]
  rw [h₁, hSC]
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

/-- A proper postcomposition only composes the two proper direct images.
Source: Stacks Project, Tags 0F7I and 0F7J
(blueprint: lem-pur-graph-proper-postcomposition).

Proof in words: take the triangle with compactifications c, ofIsProper p, and c.postcomp p.
Its open map between the compactification ambients is the identity, and its Cartesian
square has both horizontal open maps identities. Thus the exchange is the identity after
removing identity-open factors. The every-triangle composition equation leaves precisely
the associator and the canonical right-derived direct-image compositor. The three
common-refinement comparisons are rightDerivedLowerShriekIso, and their cocycle cancels
the auxiliary chosen compactifications. The identity case is the direct-image unit law;
empty opens give zero on both sides. -/
theorem graph_proper_postcomposition
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] (c : Compactification f)
    (p : Y ⟶ Z) [IsProper p] [HasCompactification (f ≫ p)] :
    Functor.isoWhiskerRight (rightDerivedLowerShriekIso A c)
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p) ≪≫
      unboundedEtaleLowerShriekCompIso A f p =
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
        (Functor.isoWhiskerLeft (rightDerivedLowerStar (ModuleCat.{u + 1} A) c.g)
          (graphChosenProperComparison A p) ≪≫
          rightDerivedLowerStarComp (ModuleCat.{u + 1} A) c.g p) ≪≫
      rightDerivedLowerShriekIso A (c.postcomp p) := by
  let F := unboundedFormalism A
  let : F.HasProperExchange := unbounded_has_proper_exchange A
  let T := postTriangle c p
  have h := F.lowerShriekCompIso_hom_eq T
  rw [unbounded_chosen_comp] at h
  simp only [F, chosen_to_model, Iso.symm_hom] at h
  rw [unbounded_shriek_iso] at h
  apply Iso.ext
  apply NatTrans.ext
  funext K
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp]
  rw [congr_app h K]
  simp only [NatTrans.comp_app, NatTrans.hcomp_app, Category.assoc]
  dsimp +instances only [T, postTriangle, unboundedFormalism,
    ExchangeFormalism.shriek, Compactification.ofIsProper]
  erw [(rightDerivedLowerShriekIso A (Compactification.ofIsProper p)).inv.naturality_assoc]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc]
  rw [model_postcomposition]
  rw [unbounded_pf_comp, Iso.symm_inv]
  rw [unbounded_sh_id]
  simp only [graphChosenProperComparison, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.map_comp, Category.assoc]
  simp only [rightDerivedLowerShriekIso, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  erw [Category.id_comp]
  rfl

end AlgebraicGeometry.Etale
