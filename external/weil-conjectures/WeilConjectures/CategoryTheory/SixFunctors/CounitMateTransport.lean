/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Whiskering

/-! # Transport of counit mates

Source: the adjunction calculation in the finite dualizing proof, paragraph 3
(blueprint: counit-mate-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory
namespace CategoryTheory

/-- Counit mates commute with compatible changes of left adjoints.

Source: the adjunction transposition in the finite dualizing proof, paragraph 3
(blueprint: counit-mate-transport).

Proof: right-adjoint uniqueness identifies the composite counits. Invert the square
of left-adjoint coefficient isomorphisms. Transpose the desired equality under the
closed B adjunction, use naturality to move both right-adjoint identifications and
substitute the two mate counit equations. The inverted square then equates the
transposes. Injectivity of the adjunction Hom equivalence finishes the proof. -/
theorem counitMates_transport
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {LO LC : C ⥤ D} {RO RC : D ⥤ C}
    {LO' LC' : C' ⥤ D'} {RO' RC' : D' ⥤ C'}
    (aO : LO ⊣ RO) (aC : LC ⊣ RC) (bO : LO' ⊣ RO') (bC : LC' ⊣ RC')
    (Q : C ⥤ C') (T : D ⥤ D')
    (tA : LO ≅ LC) (tB : LO' ≅ LC')
    (qO : LO ⋙ T ≅ Q ⋙ LO') (qC : LC ⋙ T ≅ Q ⋙ LC')
    (K : D) (K' : D') (unit : T.obj K ⟶ K')
    (uO : Q.obj (RO.obj K) ⟶ RO'.obj K')
    (uC : Q.obj (RC.obj K) ⟶ RC'.obj K')
    (hO : LO'.map uO ≫ bO.counit.app K' =
      qO.inv.app (RO.obj K) ≫ T.map (aO.counit.app K) ≫ unit)
    (hC : LC'.map uC ≫ bC.counit.app K' =
      qC.inv.app (RC.obj K) ≫ T.map (aC.counit.app K) ≫ unit)
    (hc : T.map (tA.hom.app (RO.obj K)) ≫ qC.hom.app (RO.obj K) =
      qO.hom.app (RO.obj K) ≫ tB.hom.app (Q.obj (RO.obj K))) :
    ∃ (eA : RO.obj K ≅ RC.obj K) (eB : RO'.obj K' ≅ RC'.obj K'),
      Q.map eA.hom ≫ uC = uO ≫ eB.hom := by
  let eA := (aO.ofNatIsoLeft tA).rightAdjointUniq aC
  let eB := (bO.ofNatIsoLeft tB).rightAdjointUniq bC
  refine ⟨eA.app K, eB.app K', ?_⟩
  have heA : LC.map (eA.hom.app K) ≫ aC.counit.app K =
      tA.inv.app (RO.obj K) ≫ aO.counit.app K := by
    simpa only [eA, Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_obj] using
      (aO.ofNatIsoLeft tA).rightAdjointUniq_hom_app_counit aC K
  have heB : LC'.map (eB.hom.app K') ≫ bC.counit.app K' =
      tB.inv.app (RO'.obj K') ≫ bO.counit.app K' := by
    simpa only [eB, Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_obj] using
      (bO.ofNatIsoLeft tB).rightAdjointUniq_hom_app_counit bC K'
  have hi : qC.inv.app (RO.obj K) ≫ T.map (tA.inv.app (RO.obj K)) =
      tB.inv.app (Q.obj (RO.obj K)) ≫ qO.inv.app (RO.obj K) := by
    apply (cancel_mono (T.map (tA.hom.app (RO.obj K)))).1
    apply (cancel_mono (qC.hom.app (RO.obj K))).1
    simp only [Category.assoc, ← T.map_comp, Iso.inv_hom_id_app]
    rw [hc]
    simp only [← Category.assoc, Iso.inv_hom_id_app, T.map_id]
    erw [Category.comp_id, Category.comp_id, Iso.inv_hom_id_app, Iso.inv_hom_id_app]
    rfl
  have hn := qC.inv.naturality (eA.hom.app K)
  dsimp only [Functor.comp_map] at hn
  have ht := tB.inv.naturality uO
  apply (bC.homEquiv _ _).symm.injective
  change LC'.map (Q.map (eA.hom.app K) ≫ uC) ≫ bC.counit.app K' =
    LC'.map (uO ≫ eB.hom.app K') ≫ bC.counit.app K'
  simp only [Functor.map_comp, Category.assoc]
  rw [hC, reassoc_of% hn, heB, reassoc_of% ht, hO]
  rw [← T.map_comp_assoc, heA, T.map_comp]
  simp only [← Category.assoc]
  rw [hi]

@[irreducible] private def pasteIso
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    {L : C₀ ⥤ C₁} {F : C₁ ⥤ C₂} {L' : D₀ ⥤ D₁} {F' : D₁ ⥤ D₂}
    {Q₀ : C₀ ⥤ D₀} {Q₁ : C₁ ⥤ D₁} {Q₂ : C₂ ⥤ D₂}
    (qL : L ⋙ Q₁ ≅ Q₀ ⋙ L') (qF : F ⋙ Q₂ ≅ Q₁ ⋙ F') :
    (L ⋙ F) ⋙ Q₂ ≅ Q₀ ⋙ (L' ⋙ F') :=
  NatIso.ofComponents
    (fun M ↦ (qF.app (L.obj M)) ≪≫ F'.mapIso (qL.app M)) (fun {X Y} f ↦ by
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Functor.comp_map]
      have hF := qF.hom.naturality (L.map f)
      have hL := qL.hom.naturality f
      dsimp only [Functor.comp_map] at hF hL
      rw [← Category.assoc, hF, Category.assoc, ← F'.map_comp, hL,
        Functor.map_comp, Category.assoc])

private theorem pasteIso_hom_app
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    {L : C₀ ⥤ C₁} {F : C₁ ⥤ C₂} {L' : D₀ ⥤ D₁} {F' : D₁ ⥤ D₂}
    {Q₀ : C₀ ⥤ D₀} {Q₁ : C₁ ⥤ D₁} {Q₂ : C₂ ⥤ D₂}
    (qL : L ⋙ Q₁ ≅ Q₀ ⋙ L') (qF : F ⋙ Q₂ ≅ Q₁ ⋙ F') (M : C₀) :
    (pasteIso qL qF).hom.app M =
      qF.hom.app (L.obj M) ≫ F'.map (qL.hom.app M) := by
  unfold pasteIso
  rfl

private theorem transpose_three_maps
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (a : F ⊣ G) {X : C} {Y Z W : D}
    (x : F.obj X ⟶ Y) (y : Y ⟶ Z) (z : Z ⟶ W) :
    a.homEquiv _ _ (x ≫ y) ≫ G.map z = a.homEquiv _ _ (x ≫ y ≫ z) := by
  rw [← a.homEquiv_naturality_right, Category.assoc]

private theorem transpose_counit
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (a : F ⊣ G) {X : C} {Y : D} (x : F.obj X ⟶ Y) :
    F.map (a.homEquiv _ _ x) ≫ a.counit.app Y = x := by
  change (a.homEquiv X Y).symm ((a.homEquiv X Y) x) = x
  exact (a.homEquiv X Y).symm_apply_apply x

/-- The adjunction transpose, with its argument kept abstract for large adjunctions.
Source: the counit construction (blueprint: counit-mate-transport). -/
@[irreducible] def counitTranspose
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (a : F ⊣ G) {X : C} {Y : D} (x : F.obj X ⟶ Y) : X ⟶ G.obj Y :=
  a.homEquiv X Y x

private theorem counitTranspose_counit
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (a : F ⊣ G) {X : C} {Y : D} (x : F.obj X ⟶ Y) :
    F.map (counitTranspose a x) ≫ a.counit.app Y = x := by
  unfold counitTranspose
  exact transpose_counit a x

end CategoryTheory
