/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.NatIso

/-!
# Heterogeneous equalities of morphisms and identity transports

We record small facts about morphisms which agree up to heterogeneous equality:

- `CategoryTheory.eq_eqToHom_of_heq_id`: a morphism heterogeneously equal to an identity is the
  canonical `eqToHom`;
- `CategoryTheory.comp_heq_of_heq_id` and `CategoryTheory.Functor.map_comp_heq_of_heq_id`:
  composing with a morphism heterogeneously equal to an identity does nothing;
- `CategoryTheory.map_eqToHom_conj_heq`: conjugating by transports (some of them images of
  transports under functors) does nothing up to heterogeneous equality;
- `CategoryTheory.NatIso.ofObjEqOfMapHEq`: the natural isomorphism with identity transport
  components between two functors which agree on objects and, heterogeneously, on morphisms.
-/

@[expose] public section

universe u₁ v₁

namespace CategoryTheory

/-- A morphism heterogeneously equal to an identity is the canonical `eqToHom`. -/
theorem eq_eqToHom_of_heq_id {C : Type u₁} [Category.{v₁} C] {X Y : C} (f : X ⟶ Y)
    (h : X = Y) (hf : HEq f (𝟙 X)) : f = eqToHom h := by
  subst h
  rw [eqToHom_refl]
  exact eq_of_heq hf

/-- Postcomposing with a morphism which is heterogeneously equal to an identity does not
change a morphism, up to heterogeneous equality. -/
theorem comp_heq_of_heq_id {C : Type*} [Category* C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hYZ : Y = Z) (hg : g ≍ 𝟙 Z) : f ≫ g ≍ f := by
  subst hYZ
  rw [eq_of_heq hg, Category.comp_id]

/-- Precomposing with the image of a morphism which is heterogeneously equal to an identity
does not change a morphism, up to heterogeneous equality. -/
theorem Functor.map_comp_heq_of_heq_id {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X Y : C} {Z : D} (g : X ⟶ Y) (k : F.obj Y ⟶ Z) (hXY : X = Y) (hg : g ≍ 𝟙 Y) :
    F.map g ≫ k ≍ k := by
  subst hXY
  rw [eq_of_heq hg, F.map_id, Category.id_comp]

/-- Conjugating a morphism by transport isomorphisms, two of them images of transports
under functors, does not change it up to heterogeneous equality. -/
theorem map_eqToHom_conj_heq {C C' D : Type*} [Category* C] [Category* C'] [Category* D]
    (F : C ⥤ D) (G : C' ⥤ D) {a b : C} {e e' : C'} {x y : D} (p : a = b)
    (q : F.obj b = x) (g : x ⟶ y) (r : y = G.obj e) (s : e = e') :
    F.map (eqToHom p) ≫ eqToHom q ≫ g ≫ eqToHom r ≫ G.map (eqToHom s) ≍ g := by
  cases p
  cases s
  cases q
  cases r
  simp

namespace NatIso

/-- The natural isomorphism with identity transport components between two functors which
agree on objects and, up to heterogeneous equality, on morphisms. -/
def ofObjEqOfMapHEq {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (hobj : ∀ X, F.obj X = G.obj X) (hmap : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≍ G.map f) :
    F ≅ G :=
  NatIso.ofComponents (fun X ↦ eqToIso (hobj X)) (fun f ↦ by
    simp only [eqToIso.hom]
    exact eq_of_heq ((comp_eqToHom_heq _ _).trans ((hmap f).trans (eqToHom_comp_heq _ _).symm)))

@[simp]
theorem ofObjEqOfMapHEq_hom_app {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (hobj : ∀ X, F.obj X = G.obj X) (hmap : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≍ G.map f)
    (X : C) : (ofObjEqOfMapHEq hobj hmap).hom.app X = eqToHom (hobj X) :=
  rfl

@[simp]
theorem ofObjEqOfMapHEq_inv_app {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (hobj : ∀ X, F.obj X = G.obj X) (hmap : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≍ G.map f)
    (X : C) : (ofObjEqOfMapHEq hobj hmap).inv.app X = eqToHom (hobj X).symm :=
  rfl

end NatIso

end CategoryTheory
