/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.FinCategory.Basic
import Mathlib.Data.Fintype.Sigma

/-! # Finite diagrams and Hom descent for filtered category colimits -/

@[expose] public section

universe z

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem arrow_comp_congr {C : Type z} [Category.{z} C]
    {a b c d : Arrow C} (ha : a = c) (hb : b = d)
    (h : a.right = b.left) (h' : c.right = d.left) :
    Arrow.mk (a.hom ≫ eqToHom h ≫ b.hom) =
      Arrow.mk (c.hom ≫ eqToHom h' ≫ d.hom) := by
  subst c
  subst d
  rfl

/-- Source: Stacks Project, Sites, proof of Tag 09YL, first paragraph;
Categories, Section Tag 04AX.
(blueprint: lem-weil-pbc-filtered-colimit-category-finite-functor-lift).

Proof: Enumerate the finitely many objects of D and the finitely many
arrows (the dependent sum over pairs of objects). Apply finite-list lifting to
the images under d of these enumerations. The endpoint clauses identify the
lifted arrows' endpoints with the lifted objects; transport each arrow along
these equalities to define the map of the lifted functor. The identity and
composition clauses prove its functor laws after these transports. Equality
of its composite with V j and d follows by functor extensionality: the object
images are the specified object images, and the arrow-image clause gives the
map equality with the corresponding endpoint transports. The argument includes
the empty category, where the lifted functor is empty. -/
theorem filteredColimit_category_finite_functor_lift
    (J : Type z) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{z, z}) :
    let O := colimit (F ⋙ Cat.objects)
    ∀ (_s : Category.{z} O) (V : ∀ j : J, F.obj j ⥤ O),
      (∀ (n m : ℕ) (X : Fin n → O) (A : Fin m → Arrow O),
        ∃ (j : J) (Xj : Fin n → F.obj j) (Aj : Fin m → Arrow (F.obj j)),
          (∀ q, (V j).obj (Xj q) = X q) ∧
          (∀ p, (V j).mapArrow.obj (Aj p) = A p) ∧
          (∀ p q, (A p).left = X q → (Aj p).left = Xj q) ∧
          (∀ p q, (A p).right = X q → (Aj p).right = Xj q) ∧
          (∀ p q r (h : (A p).right = (A q).left),
            Arrow.mk ((A p).hom ≫ eqToHom h ≫ (A q).hom) = A r →
            ∃ hj : (Aj p).right = (Aj q).left,
              Arrow.mk ((Aj p).hom ≫ eqToHom hj ≫ (Aj q).hom) = Aj r) ∧
          (∀ p q, A p = Arrow.mk (𝟙 (X q)) → Aj p = Arrow.mk (𝟙 (Xj q)))) →
      (∀ (D : Type z) [SmallCategory D] [FinCategory D] (d : D ⥤ O),
        ∃ (j : J) (dj : D ⥤ F.obj j), dj ⋙ V j = d) := by
  classical
  intro O s V hLift D _ _ d
  let E := Σ x y : D, x ⟶ y
  let eo := Fintype.equivFin D
  let ea := Fintype.equivFin E
  let X : Fin (Fintype.card D) → O := fun q ↦ d.obj (eo.symm q)
  let A : Fin (Fintype.card E) → Arrow O := fun p ↦
    Arrow.mk (d.map (ea.symm p).2.2)
  obtain ⟨j, Xj, Aj, hx, ha, hs, ht, hc, hi⟩ := hLift _ _ X A
  let obj : D → F.obj j := fun x ↦ Xj (eo x)
  let idx : ∀ {x y : D}, (x ⟶ y) → Fin (Fintype.card E) :=
    fun {x y} f ↦ ea ⟨x, y, f⟩
  have hA : ∀ {x y : D} (f : x ⟶ y), A (idx f) = Arrow.mk (d.map f) := by
    intro x y f
    dsimp only [A, idx]
    rw [ea.symm_apply_apply]
  have hl : ∀ {x y : D} (f : x ⟶ y), (Aj (idx f)).left = obj x := by
    intro x y f
    apply hs (idx f) (eo x)
    simp only [A, X, idx]
    rw [ea.symm_apply_apply, eo.symm_apply_apply]
    simp
  have hr : ∀ {x y : D} (f : x ⟶ y), (Aj (idx f)).right = obj y := by
    intro x y f
    apply ht (idx f) (eo y)
    simp only [A, X, idx]
    rw [ea.symm_apply_apply, eo.symm_apply_apply]
    simp
  let map : ∀ {x y : D}, (x ⟶ y) → (obj x ⟶ obj y) :=
    fun f ↦ eqToHom (hl f).symm ≫ (Aj (idx f)).hom ≫ eqToHom (hr f)
  have hmap : ∀ {x y : D} (f : x ⟶ y), Arrow.mk (map f) = Aj (idx f) := by
    intro x y f
    simp [map]
  have hid : ∀ x : D, map (𝟙 x) = 𝟙 (obj x) := by
    intro x
    apply Arrow.mk_injective
    rw [hmap]
    apply hi (idx (𝟙 x)) (eo x)
    simp only [A, X, idx]
    rw [ea.symm_apply_apply, eo.symm_apply_apply]
    simp
  have hcomp : ∀ {x y w : D} (f : x ⟶ y) (g : y ⟶ w),
      map (f ≫ g) = map f ≫ map g := by
    intro x y w f g
    have hmid : (A (idx f)).right = (A (idx g)).left := by
      rw [hA f, hA g]
      rfl
    have hfg : Arrow.mk ((A (idx f)).hom ≫ eqToHom hmid ≫ (A (idx g)).hom) =
        A (idx (f ≫ g)) := by
      have hh := arrow_comp_congr (hA f) (hA g) hmid rfl
      rw [hA (f ≫ g)]
      exact hh.trans (by simp)
    obtain ⟨hm, hmfg⟩ := hc (idx f) (idx g) (idx (f ≫ g)) hmid hfg
    apply Arrow.mk_injective
    rw [hmap (f ≫ g), ← hmfg]
    have hh := arrow_comp_congr (hmap f) (hmap g) rfl hm
    simpa using hh.symm
  let dj : D ⥤ F.obj j := { obj := obj, map := map, map_id := hid, map_comp := hcomp }
  refine ⟨j, dj, ?_⟩
  apply Arrow.functor_ext
  intro x y f
  change (V j).mapArrow.obj (Arrow.mk (map f)) = Arrow.mk (d.map f)
  rw [hmap f, ha]
  dsimp only [A, idx]
  rw [ea.symm_apply_apply]

end CategoryTheory
