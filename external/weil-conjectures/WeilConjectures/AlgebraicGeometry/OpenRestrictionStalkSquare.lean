/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor

/-! # Stalks of a commuting square of open-restricted module morphisms

Source: Stacks Project, Tag 0098; Mathlib open restriction and stalk germ formulas.
(blueprint: lem-pc-open-restriction-stalk-square).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

private def stalkOfHom {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    {M : Y.Modules} {N : X.Modules} (a : M ⟶ (Scheme.Modules.pushforward f).obj N) :
    M.presheaf.stalk (f x) ⟶ N.presheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map
    (Scheme.Modules.Hom.mapPresheaf a) ≫
      N.presheaf.stalkPushforward AddCommGrpCat.{u} f.base x

set_option backward.defeqAttrib.useBackward true in
private theorem stalkOfHom_germ {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    {M : Y.Modules} {N : X.Modules} (a : M ⟶ (Scheme.Modules.pushforward f).obj N)
    (W : Y.Opens) (hx : f x ∈ W) :
    M.presheaf.germ W (f x) hx ≫ stalkOfHom f x a =
      a.app W ≫ N.presheaf.germ (f ⁻¹ᵁ W) x hx := by
  dsimp only [stalkOfHom]
  rw [TopCat.Presheaf.stalkFunctor_map_germ_assoc]
  change a.app W ≫ ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} f.base).obj
    N.presheaf).germ W (f x) hx ≫ N.presheaf.stalkPushforward AddCommGrpCat.{u} f.base x = _
  rw [TopCat.Presheaf.stalkPushforward_germ]

set_option backward.defeqAttrib.useBackward true in
private theorem stalkOfHom_postcomp {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    {M : Y.Modules} {N Z : X.Modules} (a : M ⟶ (Scheme.Modules.pushforward f).obj N)
    (c : N ⟶ Z) :
    stalkOfHom f x (a ≫ (Scheme.Modules.pushforward f).map c) =
      stalkOfHom f x a ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (Scheme.Modules.Hom.mapPresheaf c) := by
  apply M.presheaf.stalk_hom_ext
  intro W hx
  rw [stalkOfHom_germ, ← Category.assoc, stalkOfHom_germ, Category.assoc]
  rw [TopCat.Presheaf.stalkFunctor_map_germ]
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app]
  rfl

set_option backward.defeqAttrib.useBackward true in
private theorem stalkOfHom_comp {X Y Z : Scheme.{u}}
    (g : X ⟶ Y) (f : Y ⟶ Z) (x : X) {M : Z.Modules} {N : Y.Modules} {P : X.Modules}
    (a : M ⟶ (Scheme.Modules.pushforward f).obj N)
    (b : N ⟶ (Scheme.Modules.pushforward g).obj P) :
    stalkOfHom (g ≫ f) x
        (a ≫ (Scheme.Modules.pushforward f).map b ≫
          (Scheme.Modules.pushforwardComp g f).hom.app P) =
      stalkOfHom f (g x) a ≫ stalkOfHom g x b := by
  apply M.presheaf.stalk_hom_ext
  intro W hx
  rw [stalkOfHom_germ]
  change _ = (M.presheaf.germ W (f (g x)) hx ≫ stalkOfHom f (g x) a) ≫
    stalkOfHom g x b
  rw [stalkOfHom_germ, Category.assoc, stalkOfHom_germ]
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardComp_hom_app_app]
  rfl

set_option backward.defeqAttrib.useBackward true in
private theorem stalkOfHom_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (w : f = g) (x : X)
    {M : Y.Modules} {N : X.Modules} (a : M ⟶ (Scheme.Modules.pushforward f).obj N) :
    stalkOfHom g x (a ≫ (Scheme.Modules.pushforwardCongr w).hom.app N) =
      (M.presheaf.stalkCongr (.of_eq (congrArg (fun d : X ⟶ Y ↦ d x) w.symm))).hom ≫
        stalkOfHom f x a := by
  subst g
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp]
  apply M.presheaf.stalk_hom_ext
  intro W hx
  rw [stalkOfHom_germ, stalkOfHom_germ]
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforwardCongr_hom_app_app,
    eqToHom_refl]
  simp only [op_id]
  rw [N.presheaf.map_id]
  rfl

private theorem pushforwardCongr_refl {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.Modules.pushforwardCongr (rfl : f = f) = Iso.refl (Scheme.Modules.pushforward f) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply Scheme.Modules.hom_ext
  intro W
  simp only [Scheme.Modules.pushforwardCongr_hom_app_app, eqToHom_refl, op_id,
    Iso.refl_hom, NatTrans.id_app, Scheme.Modules.Hom.id_app]
  rw [M.presheaf.map_id]
  rfl

set_option backward.defeqAttrib.useBackward true in
private theorem restriction_unit_stalk {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (x : X) (M : Y.Modules) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (j x)).map
        (Scheme.Modules.Hom.mapPresheaf ((Scheme.Modules.restrictAdjunction j).unit.app M)) ≫
      ((Scheme.Modules.restrictFunctor j).obj M).presheaf.stalkPushforward
        AddCommGrpCat.{u} j.base x = (Scheme.Modules.restrictStalkNatIso j x).inv.app M := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  apply M.presheaf.stalk_hom_ext
  intro W hx
  rw [TopCat.Presheaf.stalkFunctor_map_germ_assoc]
  simp only [Functor.comp_obj] at *
  change ((Scheme.Modules.restrictAdjunction j).unit.app M).app W ≫
    ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} j.base).obj
      ((Scheme.Modules.restrictFunctor j).obj M).presheaf).germ W (j x) hx ≫
    ((Scheme.Modules.restrictFunctor j).obj M).presheaf.stalkPushforward
      AddCommGrpCat.{u} j.base x = _
  have hpush := TopCat.Presheaf.stalkPushforward_germ AddCommGrpCat.{u} j.base
    ((Scheme.Modules.restrictFunctor j).obj M).presheaf W x hx
  rw [hpush]
  change ((Scheme.Modules.restrictAdjunction j).unit.app M).app W ≫
    ((Scheme.Modules.restrictFunctor j).obj M).presheaf.germ (j ⁻¹ᵁ W) x hx = _
  rw [Scheme.Modules.restrictAdjunction_unit_app_app]
  rw [← Scheme.Modules.germ_restrictStalkNatIso_inv_app j x M hx]
  rw [TopCat.Presheaf.germ_res_assoc]

/-- A commuting square of module morphisms remains commuting in open stalk coordinates.

Proof: represent an element of M at k(p z0) by a section s on an open W of X.
Evaluate h at W on s. The left side first applies a to s, then restricts it to
p and applies c. The right side restricts s to U, applies b, and transports the
section through the pushforward composition and congruence comparisons.
Take the germ at z0 of this section equality. The maps of additive stalks of a,
b, and c evaluate on section germs by stalkFunctor_map_germ_apply; each following
stalkPushforward changes the neighborhood to its inverse image, by
stalkPushforward_germ_apply. The inverse restriction coordinates give the germ
of the restricted section by germ_restrictStalkNatIso_inv_app, and the restriction
adjunction unit is section restriction by restrictAdjunction_unit_app_app.
The pushforward composition components and congruence components are the section
transport along pullback.condition, so their induced germ transport is precisely
stalkCongr along hp. The preimage neighborhoods on the two routes agree by this
same equality; germ_res identifies any smaller neighborhood used by restriction.
Thus the germs of the evaluated section equation are exactly the two displayed
stalk-map evaluations. Every element has a section representative, so
stalk_hom_ext gives the asserted equality of additive maps. Empty opens have no
z0. No flatness, cartesian base-change coefficient data, tensor construction,
complex or nonzero-module assumption is used.
Source: Stacks Project, Tag 0098; Mathlib/AlgebraicGeometry/Modules/Sheaf.lean
restrictAdjunction_unit_app_app and germ_restrictStalkNatIso_inv_app;
Mathlib/Topology/Sheaves/Stalks.lean stalkFunctor_map_germ_apply,
stalkPushforward_germ_apply, and germ_res_apply.
(blueprint: lem-pc-open-restriction-stalk-square). -/
theorem openRestriction_stalk_square
    {X X' : Scheme.{u}} (k : X' ⟶ X) (U : X.Opens)
    (M : X.Modules) (N : X'.Modules) (Z : (pullback k U.ι : Scheme.{u}).Modules)
    (a : M ⟶ (Scheme.Modules.pushforward k).obj N)
    (b : (Scheme.Modules.restrictFunctor U.ι).obj M ⟶
      (Scheme.Modules.pushforward (pullback.snd k U.ι)).obj Z)
    (c : (Scheme.Modules.restrictFunctor (pullback.fst k U.ι)).obj N ⟶ Z)
    (h : a ≫ (Scheme.Modules.pushforward k).map
        ((Scheme.Modules.restrictAdjunction (pullback.fst k U.ι)).unit.app N) ≫
        (Scheme.Modules.pushforward (pullback.fst k U.ι) ⋙
          Scheme.Modules.pushforward k).map c =
      (Scheme.Modules.restrictAdjunction U.ι).unit.app M ≫
        (Scheme.Modules.pushforward U.ι).map b ≫
        (Scheme.Modules.pushforwardComp (pullback.snd k U.ι) U.ι ≪≫
          Scheme.Modules.pushforwardCongr pullback.condition.symm).hom.app Z ≫
        (Scheme.Modules.pushforwardComp (pullback.fst k U.ι) k ≪≫
          Scheme.Modules.pushforwardCongr rfl).inv.app Z)
    (z0 : (pullback k U.ι : Scheme.{u})) :
    let z := pullback.fst k U.ι z0
    let q := pullback.snd k U.ι
    let L0 := RingedSpace.moduleStalkFunctor (pullback k U.ι).toRingedSpace z0
    let F0 := forget₂ (ModuleCat.{u} ((pullback k U.ι).presheaf.stalk z0)) AddCommGrpCat.{u}
    let hp : k z = U.ι (q z0) :=
      congrArg (fun d : pullback k U.ι ⟶ X ↦ d z0) pullback.condition
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (k z)).map
        (Scheme.Modules.Hom.mapPresheaf a) ≫
      N.presheaf.stalkPushforward AddCommGrpCat.{u} k.base z ≫
      (Scheme.Modules.restrictStalkNatIso (pullback.fst k U.ι) z0).inv.app N ≫
      F0.map (L0.map c) =
    (M.presheaf.stalkCongr (.of_eq hp)).hom ≫
      (Scheme.Modules.restrictStalkNatIso U.ι (q z0)).inv.app M ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (q z0)).map
        (Scheme.Modules.Hom.mapPresheaf b) ≫
      Z.presheaf.stalkPushforward AddCommGrpCat.{u} q.base z0 := by
  dsimp only
  let p := pullback.fst k U.ι
  let q := pullback.snd k U.ι
  have hh : a ≫ (Scheme.Modules.pushforward k).map
      ((Scheme.Modules.restrictAdjunction p).unit.app N ≫
        (Scheme.Modules.pushforward p).map c) ≫
      (Scheme.Modules.pushforwardComp p k).hom.app Z =
    ((Scheme.Modules.restrictAdjunction U.ι).unit.app M ≫
      (Scheme.Modules.pushforward U.ι).map b ≫
      (Scheme.Modules.pushforwardComp q U.ι).hom.app Z) ≫
      (Scheme.Modules.pushforwardCongr pullback.condition.symm).hom.app Z := by
    have t := congrArg
      (fun d ↦ d ≫ (Scheme.Modules.pushforwardComp p k).hom.app Z) h
    simp only [p, pushforwardCongr_refl, Iso.trans_refl] at t
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
      Iso.trans_hom, NatTrans.comp_app] at t
    simpa only [p, q, Category.assoc, Functor.map_comp, Functor.comp_map] using t
  have hs := congrArg (stalkOfHom (p ≫ k) z0) hh
  rw [stalkOfHom_comp, stalkOfHom_postcomp, stalkOfHom_congr, stalkOfHom_comp] at hs
  dsimp only [stalkOfHom] at hs
  rw [restriction_unit_stalk, restriction_unit_stalk] at hs
  exact hs

end AlgebraicGeometry.SingleComplexBaseChange
