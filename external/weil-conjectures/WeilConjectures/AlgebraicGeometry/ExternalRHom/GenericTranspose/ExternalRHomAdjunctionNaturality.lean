/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
/-! # Naturality of the composite global tensor--Hom adjunction

Source: Stacks 08J9 and 08JA
(blueprint: lem-pur-external-rhom-adjunction-naturality).
The transpose and evaluation use the composite adjunction and its canonical braiding.
The equations follow by adjunction naturality, curry naturality and injectivity.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v uB vB
open CategoryTheory MonoidalCategory Opposite
namespace AlgebraicGeometry.Etale.ExternalRHom.GenericTranspose
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C] {B : Type uB} [Category.{vB} B]
  {c : B ⥤ C} {s : C ⥤ B} (a : c ⊣ s)
noncomputable def tr (E K : C) (Q : B) (t : c.obj Q ⊗ E ⟶ K) :=
  (a.comp (MonoidalClosed.internalHomAdjunction₂.adj E)).homEquiv Q K
    ((β_ E (c.obj Q)).hom ≫ t)
theorem source {E E' K : C} (Q : B) (t : c.obj Q ⊗ E ⟶ K) (f : E' ⟶ E) :
    tr a E K Q t ≫ s.map ((MonoidalClosed.pre f).app K) =
      tr a E' K Q ((c.obj Q ◁ f) ≫ t) := by
  unfold tr
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  change a.homEquiv Q _ (MonoidalClosed.internalHomAdjunction₂.homEquiv _) ≫
      s.map ((MonoidalClosed.pre f).app K) =
    a.homEquiv Q _ (MonoidalClosed.internalHomAdjunction₂.homEquiv _)
  rw [← Adjunction.homEquiv_naturality_right]
  congr 1
  change MonoidalClosed.curry _ ≫ (MonoidalClosed.pre f).app K =
    MonoidalClosed.curry _
  rw [MonoidalClosed.curry_pre_app]
  congr 1
  exact BraidedCategory.braiding_naturality_left_assoc _ _ _
theorem target {E K K' : C} (Q : B) (t : c.obj Q ⊗ E ⟶ K) (k : K ⟶ K') :
    tr a E K Q t ≫ s.map ((ihom E).map k) =
      tr a E K' Q (t ≫ k) := by
  simpa only [tr, MonoidalClosed.internalHom, Functor.comp_map, Category.assoc] using
    ((a.comp (MonoidalClosed.internalHomAdjunction₂.adj E)).homEquiv_naturality_right
      ((β_ E (c.obj Q)).hom ≫ t) k).symm
theorem parameter {E K : C} {Q Q' : B} (t : c.obj Q' ⊗ E ⟶ K) (x : Q ⟶ Q') :
    x ≫ tr a E K Q' t = tr a E K Q ((c.map x ▷ E) ≫ t) := by
  unfold tr
  rw [← Adjunction.homEquiv_naturality_left]
  congr 1
  exact BraidedCategory.braiding_naturality_right_assoc _ _ _
noncomputable def ev (E K : C) : c.obj (s.obj ((ihom E).obj K)) ⊗ E ⟶ K :=
  (β_ E _).inv ≫ (a.comp (MonoidalClosed.internalHomAdjunction₂.adj E)).counit.app K
private theorem tr_ev (E K : C) : tr a E K _ (ev a E K) = 𝟙 _ := by
  simp only [tr, ev, Iso.hom_inv_id_assoc]
  rw [← (a.comp (MonoidalClosed.internalHomAdjunction₂.adj E)).homEquiv_symm_id K]
  exact ((a.comp (MonoidalClosed.internalHomAdjunction₂.adj E)).homEquiv _ _).apply_symm_apply _
private theorem injective (E K : C) (Q : B) : Function.Injective (tr a E K Q) := by
  intro t t' h
  apply (cancel_epi (β_ E (c.obj Q)).hom).1
  exact ((a.comp (MonoidalClosed.internalHomAdjunction₂.adj E)).homEquiv Q K).injective h
theorem ev_naturality {E E' K K' : C} (f : E' ⟶ E) (k : K ⟶ K') :
    (c.map (s.map ((MonoidalClosed.pre f).app K) ≫
      s.map ((ihom E').map k)) ▷ E') ≫ ev a E' K' =
    (c.obj (s.obj ((ihom E).obj K)) ◁ f) ≫ ev a E K ≫ k := by
  apply injective a E' K' _
  rw [← parameter, tr_ev, Category.comp_id]
  symm
  calc
    _ = tr a E' K _ ((c.obj (s.obj ((ihom E).obj K)) ◁ f) ≫ ev a E K) ≫
        s.map ((ihom E').map k) := by
      symm
      simpa only [Category.assoc] using
        target a _ ((c.obj (s.obj ((ihom E).obj K)) ◁ f) ≫ ev a E K) k
    _ = _ := by rw [← source, tr_ev, Category.id_comp]
end AlgebraicGeometry.Etale.ExternalRHom.GenericTranspose
