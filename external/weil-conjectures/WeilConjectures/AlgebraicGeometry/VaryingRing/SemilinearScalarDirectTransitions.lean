/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarRestriction

/-! # Transition compatibility of normalized scalar direct-image components

Source: Zheng, Construction 4.1
(blueprint: lem-sf-scalar-direct-transition-compatibility). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory Opposite
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.VaryingRing

variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
  (B : Type (u + 1)) [CommRing B] (ψ : ∀ n : ℕ, CommRingCat.of B ⟶ R n)

private def scalarPushSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : StrictTower.Modules B X) (H : Y.ProEtᵒᵖ)
    (x : ((StrictTower.moduleDirectImage B f).obj M).val.obj H) :
    M.val.obj ((Scheme.proEtaleBaseChange f).op.obj H) := x

private theorem scalarPushSection_heq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : StrictTower.Modules B X) (H : Y.ProEtᵒᵖ)
    (x : ((StrictTower.moduleDirectImage B f).obj M).val.obj H) :
    HEq (scalarPushSection B f M H x) x := HEq.rfl

private theorem scalarPushSection_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : StrictTower.Modules B X} (q : M ⟶ N) (H : Y.ProEtᵒᵖ)
    (x : ((StrictTower.moduleDirectImage B f).obj M).val.obj H) :
    scalarPushSection B f N H (((StrictTower.moduleDirectImage B f).map q).val.app H x) =
      q.val.app ((Scheme.proEtaleBaseChange f).op.obj H) (scalarPushSection B f M H x) := rfl

attribute [local irreducible] scalarPushSection

private def scalarLevelSection (C : OrdinaryScalarRestriction R φ B ψ)
    (X : Scheme.{u}) (n : ℕ) (M : Modules R φ X) (H : X.ProEtᵒᵖ)
    (x : (((C.rho X).obj M).obj (op n)).val.obj H) :
    M.val.obj (op (n, H.unop)) :=
  ((C.level X n).hom.app M).val.app H x

private theorem scalarLevelSection_heq (C : OrdinaryScalarRestriction R φ B ψ)
    (X : Scheme.{u}) (n : ℕ) (M : Modules R φ X) (H : X.ProEtᵒᵖ)
    (x : (((C.rho X).obj M).obj (op n)).val.obj H) :
    HEq (scalarLevelSection R φ B ψ C X n M H x)
      (((C.level X n).hom.app M).val.app H x) := HEq.rfl

private theorem scalarLevelSection_transition (C : OrdinaryScalarRestriction R φ B ψ)
    (X : Scheme.{u}) (M : Modules R φ X) (n : ℕ) (H : X.ProEtᵒᵖ)
    (x : (((C.rho X).obj M).obj (op (n + 1))).val.obj H) :
    scalarLevelSection R φ B ψ C X n M H
        ((((C.rho X).obj M).map (homOfLE (Nat.le_succ n)).op).val.app H x) =
      M.val.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 H.unop)).op
        (scalarLevelSection R φ B ψ C X (n + 1) M H x) :=
  C.transitions X M n H x

attribute [local irreducible] scalarLevelSection

private theorem scalarPushedLevel_heq (C : OrdinaryScalarRestriction R φ B ψ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Modules R φ X) (n : ℕ) (H : Y.ProEtᵒᵖ)
    (x : ((StrictTower.moduleDirectImage B f).obj
      (((C.rho X).obj M).obj (op n))).val.obj H) :
    HEq (scalarLevelSection R φ B ψ C X n M ((Scheme.proEtaleBaseChange f).op.obj H)
      (scalarPushSection B f (((C.rho X).obj M).obj (op n)) H x))
      (((StrictTower.moduleDirectImage B f).map ((C.level X n).hom.app M)).val.app H x) := by
  have h := scalarPushSection_heq B f
    ((res (ordinaryScalarMap R B ψ X n)).obj ((eval R φ X n).obj M)) H
    (((StrictTower.moduleDirectImage B f).map ((C.level X n).hom.app M)).val.app H x)
  rw [scalarPushSection_map] at h
  exact (scalarLevelSection_heq R φ B ψ C X n M
    ((Scheme.proEtaleBaseChange f).op.obj H) _).trans h

/-- Normalized direct-image component maps respect the successor transitions.
Source: Zheng, Construction 4.1
(blueprint: lem-sf-scalar-direct-transition-compatibility).
Proof: postcompose with the pushed level comparison, which is an isomorphism.
On sections, the normalization hd turns the source transition into C.transitions on Y.
The actual system pushforward changes the site coordinate by pro-etale base change;
it leaves the horizontal successor map unchanged, since base change preserves the
identity site arrow. Apply hd at n+1 and C.transitions on X to obtain the target
transition. The section view of pushed morphisms identifies this with the required
postcomposed target word. Extensionality and cancellation finish the equality. -/
theorem ordinaryScalarDirectComponents_step (C : OrdinaryScalarRestriction R φ B ψ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Modules R φ X)
    (d : ∀ n : ℕ, (((C.rho Y).obj ((push R φ f).obj M)).obj (op n)) ≅
      (StrictTower.moduleDirectImage B f).obj (((C.rho X).obj M).obj (op n)))
    (hd : ∀ (n : ℕ) (H : Y.ProEtᵒᵖ)
      (x : (((C.rho Y).obj ((push R φ f).obj M)).obj (op n)).val.obj H),
      HEq (((StrictTower.moduleDirectImage B f).map ((C.level X n).hom.app M)).val.app H
        ((d n).hom.val.app H x))
        (((C.level Y n).hom.app ((push R φ f).obj M)).val.app H x))
    (n : ℕ) :
    (((C.rho Y).obj ((push R φ f).obj M)).map (homOfLE (Nat.le_succ n)).op) ≫
        (d n).hom =
      (d (n + 1)).hom ≫ (StrictTower.moduleDirectImage B f).map
        (((C.rho X).obj M).map (homOfLE (Nat.le_succ n)).op) := by
  apply (cancel_mono ((StrictTower.moduleDirectImage B f).map
    ((C.level X n).hom.app M))).1
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro H
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  have hd' (i : ℕ)
      (t : (((C.rho Y).obj ((push R φ f).obj M)).obj (op i)).val.obj H) :=
    (scalarPushedLevel_heq R φ B ψ C f M i H ((d i).hom.val.app H t)).trans
      ((hd i H t).trans
        (scalarLevelSection_heq R φ B ψ C Y i ((push R φ f).obj M) H t).symm)
  let tx := ((((C.rho Y).obj ((push R φ f).obj M)).map
    (homOfLE (Nat.le_succ n)).op).val.app H x)
  have hLeft := (scalarPushedLevel_heq R φ B ψ C f M n H
    ((d n).hom.val.app H tx)).symm
  have hL := hd' n tx
  have hY := scalarLevelSection_transition R φ B ψ C Y ((push R φ f).obj M) n H x
  let z := scalarPushSection B f (((C.rho X).obj M).obj (op (n + 1))) H
    ((d (n + 1)).hom.val.app H x)
  have hX := scalarLevelSection_transition R φ B ψ C X M n
    ((Scheme.proEtaleBaseChange f).op.obj H) z
  have hS := hd' (n + 1) x
  have hR := scalarPushedLevel_heq R φ B ψ C f M n H
    (((StrictTower.moduleDirectImage B f).map
      (((C.rho X).obj M).map (homOfLE (Nat.le_succ n)).op)).val.app H
        ((d (n + 1)).hom.val.app H x))
  rw [scalarPushSection_map] at hR
  let y : M.val.obj (op (n + 1, (Scheme.proEtaleBaseChange f).obj H.unop)) :=
    scalarLevelSection R φ B ψ C Y (n + 1) ((push R φ f).obj M) H x
  have hP : ((push R φ f).obj M).val.map
      (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 H.unop)).op y =
      M.val.map (Prod.mkHom (homOfLE (Nat.le_succ n))
        (𝟙 ((Scheme.proEtaleBaseChange f).obj H.unop))).op y := by
    change M.val.map ((baseChange f).map
      (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 H.unop))).op y = _
    have hb : (baseChange f).map
        (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 H.unop)) =
        Prod.mkHom (homOfLE (Nat.le_succ n))
          (𝟙 ((Scheme.proEtaleBaseChange f).obj H.unop)) := by
      apply Prod.hom_ext
      · rfl
      · exact (Scheme.proEtaleBaseChange f).map_id _
    rw [hb]
    rfl
  have hC := congrArg
    (fun t : M.val.obj (op (n + 1, (Scheme.proEtaleBaseChange f).obj H.unop)) ↦
      M.val.map (Prod.mkHom (homOfLE (Nat.le_succ n))
        (𝟙 ((Scheme.proEtaleBaseChange f).obj H.unop))).op t)
    (eq_of_heq hS).symm
  have h1 := hLeft.trans (hL.trans (heq_of_eq hY))
  have h2 := h1.trans (heq_of_eq hP)
  have h3 := h2.trans (heq_of_eq hC)
  have h4 := h3.trans (heq_of_eq hX.symm)
  exact eq_of_heq (h4.trans hR)

end AlgebraicGeometry.ProEtale.VaryingRing
