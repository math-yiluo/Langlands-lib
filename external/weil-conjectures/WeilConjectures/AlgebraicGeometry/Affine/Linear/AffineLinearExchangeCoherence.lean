/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearTraceAction
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
/-! # Exchange pasting for the linear compact-support action

Source: linear trace invariance, proof paragraph 1, functoriality of the action.
(blueprint: lem-amb-affine-linear-exchange-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pasting of ordinary derived compact-support exchange maps, in the left-derived
inverse-image model. Source: linear trace proof, paragraph 1; transport of the existing
unbounded exchange pasting equation through the exact/derived comparison.
(blueprint: lem-amb-affine-linear-exchange-coherence). -/
theorem affineLinearExchange_paste (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian Y] [IsNoetherian Y'] [IsNoetherian Y'']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w)
    (K : DerivedCategoryModule A X) :
    (ordinaryFinitePullback A w).map ((rightDerivedLowerShriekBaseChangeMap A sq₁).app K) ≫
        (rightDerivedLowerShriekBaseChangeMap A sq₂).app
          ((ordinaryFinitePullback A v').obj K) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v).inv.app _ ≫
        (rightDerivedLowerShriekBaseChangeMap A (sq₂.paste_horiz sq₁)).app K ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'').map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v').hom.app K) := by
  have h := congr_app (unboundedEtaleCompactSupport_baseChange_comp A sq₁ sq₂
    (sq₂.paste_horiz sq₁)) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    unboundedEtaleCompactSupportBaseChange,
    unboundedEtaleUpperStarCompIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, Functor.map_comp, Category.assoc] at h
  apply (cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v).hom.app _)).mp
  apply (cancel_mono ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'').map
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v').inv.app K))).mp
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app]
  apply (cancel_epi ((leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} A) (w ≫ v)).inv.app _)).mp
  apply (cancel_mono ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'').map
    ((leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} A) (w' ≫ v')).hom.app K))).mp
  simp only [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Category.assoc, Iso.inv_hom_id_app_assoc,
    Functor.map_comp]
  simp only [leftDerivedUpperStarIsoMapDerivedCategory, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app, Category.comp_id] at h ⊢
  simp only [Category.id_comp]
  rw [h]
  simp only [Functor.map_comp, ordinaryFinitePullback]
  have hn :=
    (upperStar (ModuleCat.{u + 1} A) w).leftDerivedFunctorIsoMapDerivedCategory.inv.naturality
    ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f').map
      ((upperStar (ModuleCat.{u + 1} A) v').leftDerivedFunctorIsoMapDerivedCategory.hom.app K))
  rw [reassoc_of% hn]
  have he := (rightDerivedLowerShriekBaseChangeMap A sq₂).naturality
    ((upperStar (ModuleCat.{u + 1} A) v').leftDerivedFunctorIsoMapDerivedCategory.hom.app K)
  simp only [Functor.comp_map] at he
  rw [reassoc_of% he]
  rw [← Functor.map_comp_assoc]
  rw [← (upperStar (ModuleCat.{u + 1} A) w').leftDerivedFunctorIsoMapDerivedCategory.hom.naturality]
  simp only [Functor.map_comp, Category.assoc]
  have hlast :=
    (upperStar (ModuleCat.{u + 1} A) w).leftDerivedFunctorIsoMapDerivedCategory.inv.naturality
      ((rightDerivedLowerShriekBaseChangeMap A sq₁).app K)
  simp only [Functor.comp_obj] at hlast
  rw [← reassoc_of% hlast]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exchange_paste'
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian Y] [IsNoetherian Y'] [IsNoetherian Y'']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w)
    (z : X'' ⟶ X) (b : Y'' ⟶ Y) (hz : z = w' ≫ v') (hb : b = w ≫ v)
    (sq : IsPullback z f'' f b) (K : DerivedCategoryModule A X) :
    (ordinaryFinitePullback A w).map ((rightDerivedLowerShriekBaseChangeMap A sq₁).app K) ≫
        (rightDerivedLowerShriekBaseChangeMap A sq₂).app
          ((ordinaryFinitePullback A v').obj K) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v b hb).inv.app _ ≫
        (rightDerivedLowerShriekBaseChangeMap A sq).app K ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'').map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v' z hz).hom.app K) := by
  subst hz hb
  exact affineLinearExchange_paste A sq₁ sq₂ K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comp_id_right_inv
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (K : DerivedCategoryModule A Y) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g (𝟙 Y) g
      (Category.comp_id g).symm).inv.app K =
      (ordinaryFinitePullback A g).map ((leftDerivedUpperStarId
        (ModuleCat.{u + 1} A) Y).hom.app K) := by
  apply (cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g (𝟙 Y) g
    (Category.comp_id g).symm).hom.app K)).mp
  simpa only [Iso.hom_inv_id_app, ordinaryFinitePullback, Functor.id_obj] using
    (leftDerivedUpperStarComp_id_right_hom_app (ModuleCat.{u + 1} A) g K).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comp_id_left_inv
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (K : DerivedCategoryModule A Y) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (𝟙 X) g g
      (Category.id_comp g).symm).inv.app K =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).hom.app
        ((ordinaryFinitePullback A g).obj K) := by
  apply (cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (𝟙 X) g g
    (Category.id_comp g).symm).hom.app K)).mp
  simpa only [Iso.hom_inv_id_app, ordinaryFinitePullback, Functor.id_obj] using
    (leftDerivedUpperStarComp_id_left_hom_app (ModuleCat.{u + 1} A) g K).symm

private theorem square_inv_eq
    (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}} {v : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq v f' f g)
    (z : X' ⟶ Y) (hz : z = v ≫ f) (K : DerivedCategoryModule A Y) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv.app K =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v f z hz).inv.app K ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f' g z (hz.trans sq.w)).hom.app K := by
  subst hz
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pasting the automorphism square before and after a base-change square gives
compatible action maps. Source: linear trace proof, paragraph 1; apply exchange pasting
in the two orders and cancel the identity pullback comparisons.
(blueprint: lem-amb-affine-linear-exchange-coherence). -/
theorem affineLinearExchange_action
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : X' ⟶ X} {g : Y' ⟶ Y} {a : X ⟶ X} {a' : X' ⟶ X'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f'] [LocallyOfFiniteType f']
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback v f' f g) (sa : IsPullback a f f (𝟙 Y))
    (sa' : IsPullback a' f' f' (𝟙 Y')) (hw : a' ≫ v = v ≫ a)
    (K : DerivedCategoryModule A X) :
    (ordinaryFinitePullback A g).map
        ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) Y).inv.app _ ≫
          (rightDerivedLowerShriekBaseChangeMap A sa).app K) ≫
        (rightDerivedLowerShriekBaseChangeMap A sq).app
          ((ordinaryFinitePullback A a).obj K) =
      (rightDerivedLowerShriekBaseChangeMap A sq).app K ≫
        (leftDerivedUpperStarId (ModuleCat.{u + 1} A) Y').inv.app _ ≫
        (rightDerivedLowerShriekBaseChangeMap A sa').app
          ((ordinaryFinitePullback A v).obj K) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f').map
          ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) (CommSq.mk hw)).inv.app K) := by
  have so : IsPullback (v ≫ a) f' f g := by
    simpa only [Category.comp_id] using sq.paste_horiz sa
  have h₁ := exchange_paste' A sa sq (v ≫ a) g rfl (Category.comp_id g).symm so K
  have h₂ := exchange_paste' A sq sa' (v ≫ a) g hw.symm (Category.id_comp g).symm so K
  rw [comp_id_right_inv] at h₁
  rw [comp_id_left_inv] at h₂
  have h₂' := congrArg (fun z ↦
    (leftDerivedUpperStarId (ModuleCat.{u + 1} A) Y').inv.app _ ≫ z) h₂
  dsimp only [ordinaryFinitePullback] at h₁ h₂ h₂' ⊢
  simp only [Functor.comp_obj] at h₂'
  rw [Iso.inv_hom_id_app_assoc] at h₂'
  have hn := (leftDerivedUpperStarId (ModuleCat.{u + 1} A) Y').inv.naturality
    ((rightDerivedLowerShriekBaseChangeMap A sq).app K)
  simp only [Functor.id_map, Functor.comp_obj] at hn
  rw [← Category.assoc, ← hn, Category.assoc] at h₂'
  rw [square_inv_eq A (CommSq.mk hw) (v ≫ a) hw.symm K]
  simp only [Functor.map_comp, Category.assoc]
  rw [h₁]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% h₂']
  simp only [← Functor.map_comp, Iso.hom_inv_id_app_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An equivariant coefficient map induces an equivariant compact-support exchange.
Source: linear trace proof, paragraph 1; combine action pasting with naturality in the
coefficient and the identity inverse-image comparison.
(blueprint: lem-amb-affine-linear-exchange-coherence). -/
theorem affineLinearExchange_action_naturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : X' ⟶ X} {g : Y' ⟶ Y} {a : X ⟶ X} {a' : X' ⟶ X'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f'] [LocallyOfFiniteType f']
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback v f' f g) (sa : IsPullback a f f (𝟙 Y))
    (sa' : IsPullback a' f' f' (𝟙 Y')) (hw : a' ≫ v = v ≫ a)
    (K : DerivedCategoryModule A X) (K' : DerivedCategoryModule A X')
    (theta : (ordinaryFinitePullback A a).obj K ⟶ K)
    (theta' : (ordinaryFinitePullback A a').obj K' ⟶ K')
    (b : (ordinaryFinitePullback A v).obj K ⟶ K')
    (hb : (ordinaryFinitePullback A a').map b ≫ theta' =
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) (CommSq.mk hw)).inv.app K ≫
        (ordinaryFinitePullback A v).map theta ≫ b) :
    (ordinaryFinitePullback A g).map
        ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) Y).inv.app _ ≫
          (rightDerivedLowerShriekBaseChangeMap A sa).app K ≫
          (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map theta) ≫
        (rightDerivedLowerShriekBaseChangeMap A sq).app K ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f').map b =
      (rightDerivedLowerShriekBaseChangeMap A sq).app K ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f').map b ≫
        (leftDerivedUpperStarId (ModuleCat.{u + 1} A) Y').inv.app
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f').obj K') ≫
        (rightDerivedLowerShriekBaseChangeMap A sa').app K' ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f').map theta' := by
  simp only [Functor.map_comp, Category.assoc]
  have hn := (rightDerivedLowerShriekBaseChangeMap A sq).naturality theta
  simp only [Functor.comp_map] at hn
  change (ordinaryFinitePullback A g).map
    ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map theta) ≫
      (rightDerivedLowerShriekBaseChangeMap A sq).app K = _ at hn
  have he := affineLinearExchange_action A sq sa sa' hw K
  simp only [Functor.map_comp, Category.assoc] at he
  erw [reassoc_of% hn, reassoc_of% he]
  erw [← Functor.map_comp_assoc, ← Functor.map_comp]
  simp only [Category.assoc]
  erw [← hb]
  simp only [Functor.map_comp]
  have hn' := (rightDerivedLowerShriekBaseChangeMap A sa').naturality b
  simp only [Functor.comp_map] at hn'
  erw [← reassoc_of% hn']
  have hi := (leftDerivedUpperStarId (ModuleCat.{u + 1} A) Y').inv.naturality
    ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f').map b)
  simp only [Functor.id_map] at hi
  erw [← reassoc_of% hi]
end AlgebraicGeometry.Etale
