/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.EpiMono

/-!
# Split epimorphisms in composites with isomorphisms

If a composite `a ≫ b ≫ φ ≫ c` is an isomorphism and `c` is an isomorphism, then `φ` is a split
epimorphism. If moreover `b` is a split epimorphism and `a` is an isomorphism, then `b` is an
isomorphism. If `p ≫ i = b ≫ s` is an epi–mono factorisation with `s ≫ b = 𝟙`, then `i ≫ b` is
an isomorphism (`CategoryTheory.isIso_comp_of_fac`). A morphism with an inverse up to
isomorphisms on both sides is an isomorphism (`CategoryTheory.isIso_of_isIso_comp_of_isIso_comp`).
A natural transformation that is a split monomorphism at an object is one at every isomorphic
object (`CategoryTheory.NatTrans.isSplitMono_app_of_iso`).
-/

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {A B D E F : C}

/-- If `a ≫ b ≫ φ ≫ c` is an isomorphism and `c` is an isomorphism, then `φ` is a split
epimorphism, with section `c ≫ (a ≫ b ≫ φ ≫ c)⁻¹ ≫ a ≫ b`. -/
lemma isSplitEpi_of_isIso_comp (a : A ⟶ B) (b : B ⟶ D) (φ : D ⟶ E) (c : E ⟶ F) [IsIso c]
    (h : IsIso (a ≫ b ≫ φ ≫ c)) : IsSplitEpi φ :=
  IsSplitEpi.mk' ⟨c ≫ inv (a ≫ b ≫ φ ≫ c) ≫ a ≫ b, by
    rw [← cancel_mono c]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]⟩

/-- If `a ≫ x ≫ y ≫ c` is an isomorphism, `a` and `c` are isomorphisms and `x` is a split
epimorphism, then `x` is an isomorphism: it is a monomorphism since `x ≫ y` is one. -/
lemma isIso_of_isIso_comp_of_isSplitEpi (a : A ⟶ B) (x : B ⟶ D) (y : D ⟶ E) (c : E ⟶ F)
    [IsIso a] [IsIso c] [IsSplitEpi x] (h : IsIso (a ≫ x ≫ y ≫ c)) : IsIso x := by
  have : IsIso (x ≫ y ≫ c) := IsIso.of_isIso_comp_left a _
  have : IsIso ((x ≫ y) ≫ c) := by rwa [Category.assoc]
  have : IsIso (x ≫ y) := IsIso.of_isIso_comp_right (x ≫ y) c
  have : Mono x := mono_of_mono x y
  exact isIso_of_mono_of_isSplitEpi x

/-- If a morphism has an epi–mono factorisation `p ≫ i` and also factors as `b ≫ s` through an
object `B` with `s ≫ b = 𝟙 B`, then `i ≫ b` is an isomorphism, with inverse `s ≫ p`: the image of
`p ≫ i` is identified with `B`. -/
lemma isIso_comp_of_fac {M P : C} (p : M ⟶ P) (i : P ⟶ M) (b : M ⟶ B) (s : B ⟶ M) [Epi p]
    [Mono i] (h : p ≫ i = b ≫ s) (hs : s ≫ b = 𝟙 B) : IsIso (i ≫ b) := by
  refine ⟨s ≫ p, ?_, by rw [Category.assoc, reassoc_of% h, reassoc_of% hs, hs]⟩
  rw [← cancel_mono i, ← cancel_epi p]
  simp only [Category.assoc, Category.id_comp]
  rw [reassoc_of% h, reassoc_of% hs, h, reassoc_of% hs]


/-- A morphism `a` such that `a ≫ b` and `b ≫ a` are isomorphisms for some `b` is an
isomorphism. -/
lemma isIso_of_isIso_comp_of_isIso_comp {P Q : C} (a : P ⟶ Q) (b : Q ⟶ P) (h₁ : IsIso (a ≫ b))
    (h₂ : IsIso (b ≫ a)) : IsIso a := by
  have : IsSplitMono a := IsSplitMono.mk' ⟨b ≫ inv (a ≫ b), by rw [← Category.assoc,
    IsIso.hom_inv_id]⟩
  have : IsSplitEpi a := IsSplitEpi.mk' ⟨inv (b ≫ a) ≫ b, by rw [Category.assoc, IsIso.inv_hom_id]⟩
  exact isIso_of_epi_of_isSplitMono a

/-- A natural transformation that is a split monomorphism at `Y` is one at any `X ≅ Y`. -/
lemma NatTrans.isSplitMono_app_of_iso {D : Type*} [Category D] {F G : C ⥤ D} (α : F ⟶ G)
    {X Y : C} (e : X ≅ Y) (h : IsSplitMono (α.app Y)) : IsSplitMono (α.app X) := by
  have hX : α.app X = F.map e.hom ≫ α.app Y ≫ G.map e.inv := by
    rw [α.naturality_assoc, ← G.map_comp, e.hom_inv_id, G.map_id, Category.comp_id]
  rw [hX]
  infer_instance

end CategoryTheory
