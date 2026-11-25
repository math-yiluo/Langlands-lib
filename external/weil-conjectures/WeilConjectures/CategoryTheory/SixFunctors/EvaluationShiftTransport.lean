/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor

/-! # Evaluation detects compatibility of dual shifts with scalar extension -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option linter.unusedSimpArgs false
universe u v
open CategoryTheory Opposite
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

private theorem tensor_second_comp {C : Type*} [Category C] (B : C × C ⥤ C)
    (K : C) {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) :
    B.map (Prod.mkHom (𝟙 K) (f ≫ g)) =
      B.map (Prod.mkHom (𝟙 K) f) ≫ B.map (Prod.mkHom (𝟙 K) g) := by
  rw [← B.map_comp]
  simp

/-- A normalized scalar evaluation square commutes with the specified dual shifts,
provided the tensor cancellation maps commute with scalar extension.
Source: blueprint thm-coef-qbar-verdier, tensor--Hom transpose in steps 3--4.
(blueprint: lem-coef-evaluation-shift-transport-X3).
Proof: cancel the target dual shift and test both maps by evaluation. Naturality
of tensor cancellation moves beta through that evaluation. The normalized beta
square, followed by the scalar tensor cancellation square and naturality of the
binary comparison, gives the source normalization square. Cancel the scalar
source-shift isomorphism to obtain the claimed equality. The proof uses only
injectivity of evaluation and naturality of tensor cancellation. -/
theorem evaluation_shift_transport
    {C : Type u} [Category C] {D : Type v} [Category D]
    [HasShift C ℤ] [HasShift D ℤ]
    (B : C × C ⥤ C) (U : D × D ⥤ D) (T : C ⥤ D) [T.CommShift ℤ]
    (d : Cᵒᵖ ⥤ C) (e : Dᵒᵖ ⥤ D)
    (w : C) (z : D)
    (ev : ∀ K, B.obj (K, d.obj (op K)) ⟶ w)
    (ew : ∀ K, U.obj (K, e.obj (op K)) ⟶ z)
    (detect : ∀ (K P : D) (f g : P ⟶ e.obj (op K)),
      U.map (Prod.mkHom (𝟙 K) f) ≫ ew K =
        U.map (Prod.mkHom (𝟙 K) g) ≫ ew K → f = g)
    (ewnat : ∀ {K M : D} (f : K ⟶ M),
      U.map (Prod.mkHom f (𝟙 _)) ≫ ew M =
        U.map (Prod.mkHom (𝟙 K) (e.map f.op)) ≫ ew K)
    (mu : B ⋙ T ≅ T.prod T ⋙ U) (omega : T.obj w ⟶ z)
    (beta : d ⋙ T ⟶ T.op ⋙ e)
    (hbeta : ∀ K,
      U.map (Prod.mkHom (𝟙 (T.obj K)) (beta.app (op K))) ≫ ew (T.obj K) =
        mu.inv.app (K, d.obj (op K)) ≫ T.map (ev K) ≫ omega)
    (n : ℤ)
    (sd : ∀ K : C, d.obj (op (K⟦-n⟧)) ≅ (d.obj (op K))⟦n⟧)
    (se : ∀ K : D, e.obj (op (K⟦-n⟧)) ≅ (e.obj (op K))⟦n⟧)
    (c : ∀ K P, B.obj (K⟦-n⟧, P⟦n⟧) ⟶ B.obj (K, P))
    (c' : ∀ K P, U.obj (K⟦-n⟧, P⟦n⟧) ⟶ U.obj (K, P))
    (cnat : ∀ K {P Q : D} (f : P ⟶ Q),
      U.map (Prod.mkHom (𝟙 (K⟦-n⟧)) (f⟦n⟧')) ≫ c' K Q =
        c' K P ≫ U.map (Prod.mkHom (𝟙 K) f))
    (hnorm : ∀ K,
      B.map (Prod.mkHom (𝟙 (K⟦-n⟧)) ((sd K).inv)) ≫
        ev (K⟦-n⟧) = c K (d.obj (op K)) ≫ ev K)
    (hnorm' : ∀ K,
      U.map (Prod.mkHom (𝟙 (K⟦-n⟧)) ((se K).inv)) ≫
        ew (K⟦-n⟧) = c' K (e.obj (op K)) ≫ ew K)
    (hscalar : ∀ K P,
      U.map (Prod.mkHom ((T.commShiftIso (-n)).hom.app K)
          ((T.commShiftIso n).hom.app P)) ≫
        c' (T.obj K) (T.obj P) ≫ mu.inv.app (K, P) =
      mu.inv.app (K⟦-n⟧, P⟦n⟧) ≫ T.map (c K P)) (K : C) :
    T.map ((sd K).hom) ≫
        ((T.commShiftIso n).hom.app (d.obj (op K))) ≫ (beta.app (op K))⟦n⟧' =
      beta.app (op (K⟦-n⟧)) ≫
        e.map (((T.commShiftIso (-n)).inv.app K).op) ≫
          (se (T.obj K)).hom := by
  have hn : B.map (Prod.mkHom (𝟙 (K⟦-n⟧)) ((sd K).hom)) ≫
      c K (d.obj (op K)) ≫ ev K = ev (K⟦-n⟧) := by
    rw [← hnorm]
    simp only [← B.map_comp_assoc, prod_comp, Category.id_comp,
      Iso.hom_inv_id, ← prod_id, B.map_id, Category.id_comp]
  apply (cancel_mono ((se (T.obj K)).inv)).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply detect ((T.obj K)⟦-n⟧) _
  simp only [tensor_second_comp, Category.assoc]
  rw [hnorm']
  dsimp only [Functor.op_obj, Functor.comp_obj] at *
  erw [reassoc_of% (cnat (T.obj K) (beta.app (op K)))]
  rw [hbeta]
  have : IsIso (Prod.mkHom ((T.commShiftIso (-n)).hom.app K)
      (𝟙 (T.obj (d.obj (op (K⟦-n⟧)))))) :=
    (Iso.prod ((T.commShiftIso (-n)).app K) (Iso.refl _)).isIso_hom
  apply (cancel_epi (U.map (Prod.mkHom ((T.commShiftIso (-n)).hom.app K)
    (𝟙 (T.obj (d.obj (op (K⟦-n⟧)))))))).1
  have hr :
      U.map (Prod.mkHom ((T.commShiftIso (-n)).hom.app K)
          (𝟙 (T.obj (d.obj (op (K⟦-n⟧)))))) ≫
        U.map (Prod.mkHom (𝟙 ((T.obj K)⟦-n⟧)) (beta.app (op (K⟦-n⟧)))) ≫
        U.map (Prod.mkHom (𝟙 ((T.obj K)⟦-n⟧))
          (e.map (((T.commShiftIso (-n)).inv.app K).op))) ≫ ew ((T.obj K)⟦-n⟧) =
      U.map (Prod.mkHom (𝟙 (T.obj (K⟦-n⟧))) (beta.app (op (K⟦-n⟧)))) ≫
        ew (T.obj (K⟦-n⟧)) := by
    rw [← ewnat]
    simp only [← U.map_comp_assoc, prod_comp,
      Category.comp_id, Category.id_comp, Iso.hom_inv_id_app,
      Functor.comp_obj]
    congr 2; simp
  rw [hr, hbeta]
  have hi :
      U.map (Prod.mkHom ((T.commShiftIso (-n)).hom.app K)
          (𝟙 (T.obj (d.obj (op (K⟦-n⟧)))))) ≫
        U.map (Prod.mkHom (𝟙 ((T.obj K)⟦-n⟧))
          (T.map ((sd K).hom))) ≫
        U.map (Prod.mkHom (𝟙 ((T.obj K)⟦-n⟧))
          ((T.commShiftIso n).hom.app (d.obj (op K)))) =
      U.map (Prod.mkHom (𝟙 (T.obj (K⟦-n⟧)))
          (T.map ((sd K).hom))) ≫
        U.map (Prod.mkHom ((T.commShiftIso (-n)).hom.app K)
          ((T.commShiftIso n).hom.app (d.obj (op K)))) := by
    simp only [← U.map_comp, prod_comp, Category.comp_id, Category.id_comp]
    congr 2; simp
  rw [reassoc_of% hi, reassoc_of% (hscalar K (d.obj (op K)))]
  have hm := mu.inv.naturality
    (Prod.mkHom (𝟙 (K⟦-n⟧)) ((sd K).hom))
  dsimp only [Functor.comp_map, Functor.prod_map] at hm
  rw [T.map_id] at hm
  rw [reassoc_of% hm]
  rw [← T.map_comp_assoc, ← T.map_comp_assoc, Category.assoc, hn]

/-- The actual dual shift, with its opposite source identified explicitly. -/
def reindexedDualShift {C : Type u} [Category C] [HasShift C ℤ]
    (d : Cᵒᵖ ⥤ C) [d.CommShift ℤ] (n : ℤ) (K : C) :
    d.obj (op (K⟦-n⟧)) ≅ (d.obj (op K))⟦n⟧ :=
  (d.mapIso ((shiftFunctorOpIso C n (-n) (add_neg_cancel n)).app (op K))).symm ≪≫
    (d.commShiftIso n).app (op K)

/-- Objectwise compatibility for reindexed shifts gives compatibility of the
contravariant composite functors. -/
theorem commShift_of_reindexed_components
    {C : Type u} [Category C] {D : Type v} [Category D]
    [HasShift C ℤ] [HasShift D ℤ]
    (T : C ⥤ D) [T.CommShift ℤ]
    (d : Cᵒᵖ ⥤ C) (e : Dᵒᵖ ⥤ D) [d.CommShift ℤ] [e.CommShift ℤ]
    (beta : d ⋙ T ⟶ T.op ⋙ e)
    (h : ∀ n K,
      T.map (reindexedDualShift d n K).hom ≫
          (T.commShiftIso n).hom.app (d.obj (op K)) ≫ (beta.app (op K))⟦n⟧' =
        beta.app (op (K⟦-n⟧)) ≫ e.map (((T.commShiftIso (-n)).inv.app K).op) ≫
          (reindexedDualShift e n (T.obj K)).hom) :
    NatTrans.CommShift beta ℤ := by
  constructor
  intro n
  ext K
  have hh := h n K.unop
  dsimp only [reindexedDualShift, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_inv, Iso.app_inv, Iso.app_hom] at hh
  apply (cancel_epi (T.map (d.map
    ((shiftFunctorOpIso C n (-n) (add_neg_cancel n)).inv.app K)))).1
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.commShiftIso_comp_hom_app, Functor.op_commShiftIso_hom_app
      _ _ n (-n) (add_neg_cancel n), Functor.op_map, e.map_comp, Category.assoc]
  have hb := beta.naturality
    ((shiftFunctorOpIso C n (-n) (add_neg_cancel n)).inv.app K)
  dsimp only [Functor.comp_map, Functor.op_map] at hb
  rw [reassoc_of% hb]
  have hc :
      (T.map ((shiftFunctorOpIso C n (-n) (add_neg_cancel n)).inv.app K).unop).op ≫
        (T.map ((shiftFunctorOpIso C n (-n) (add_neg_cancel n)).hom.app K).unop).op =
      𝟙 _ := by
    rw [← op_comp, ← T.map_comp, ← unop_comp, Iso.inv_hom_id_app,
      unop_id, T.map_id, op_id]
  rw [← e.map_comp_assoc, hc]
  erw [e.map_id, Category.id_comp]
  simpa only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
    Functor.comp_obj, Functor.op_obj, op_unop, T.map_comp, Category.assoc] using hh

end CategoryTheory
