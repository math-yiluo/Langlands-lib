/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.SequentialProduct

/-!
# Countable AB4* from sequential limits of epimorphisms

Let `C` be a category with countable products in which, for every tower of epimorphisms
`⋯ ⟶ X₁ ⟶ X₀`, the projection `lim Xₙ ⟶ X₀` is an epimorphism. Then countable products of
epimorphisms are epimorphisms, and if `C` is abelian, it satisfies countable AB4\*. This
abstracts the argument of `Mathlib/Condensed/Light/Epi.lean` and `Mathlib/Condensed/Light/AB.lean`.

## Main statements

* `CategoryTheory.Limits.epi_pi_map_of_epi_π_app_zero`: countable products of epimorphisms are
  epimorphisms.
* `CategoryTheory.CountableAB4Star.of_epi_π_app_zero`: countable AB4\* holds.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type*} [Category* C]

/-- In `C`, the projection `lim Xₙ ⟶ X₀` of a tower of epimorphisms `⋯ ⟶ X₁ ⟶ X₀` is an
epimorphism. -/
def EpiπAppZeroOfEpi (C : Type*) [Category* C] : Prop :=
  ∀ ⦃F : ℕᵒᵖ ⥤ C⦄ ⦃c : Cone F⦄, IsLimit c →
    (∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op)) → Epi (c.π.app ⟨0⟩)

namespace Limits

open SequentialProduct

attribute [local instance] functorMap_epi

/-- If sequential limits of epimorphisms project epimorphically onto the first term, countable
products of epimorphisms are epimorphisms. -/
lemma epi_pi_map_of_epi_π_app_zero [HasCountableProducts C] [HasZeroMorphisms C]
    [HasFiniteBiproducts C] (h : EpiπAppZeroOfEpi C) {M N : ℕ → C} (f : ∀ n, M n ⟶ N n)
    [∀ n, Epi (f n)] : Epi (Limits.Pi.map f) := by
  have := h (isLimit f) fun n ↦ by
    simp only [Nat.succ_eq_add_one, homOfLE_leOfHom, Functor.ofOpSequence_map_homOfLE_succ]
    infer_instance
  have hπ : (cone f).π.app ⟨0⟩ = Limits.Pi.map f ≫
      Limits.Pi.map fun m ↦ eqToHom (functorObj_eq_neg (Nat.not_lt_zero m)).symm := by
    simp [cone_π_app]
  rw [← Category.comp_id (Limits.Pi.map f), ← IsIso.hom_inv_id (Limits.Pi.map fun m ↦
    eqToHom (functorObj_eq_neg (Nat.not_lt_zero m)).symm), ← Category.assoc, ← hπ]
  infer_instance

/-- If sequential limits of epimorphisms project epimorphically onto the first term, the functor
`lim : (Discrete ℕ ⥤ C) ⥤ C` preserves epimorphisms. -/
lemma lim_preservesEpimorphisms_of_epi_π_app_zero [HasCountableProducts C] [HasZeroMorphisms C]
    [HasFiniteBiproducts C] [HasPushouts C] (h : EpiπAppZeroOfEpi C) :
    (lim (J := Discrete ℕ) (C := C)).PreservesEpimorphisms where
  preserves f _ := by
    have := epi_pi_map_of_epi_π_app_zero h (f.app ⟨·⟩)
    have : lim.map f = (Pi.isoLimit _).inv ≫ Limits.Pi.map (f.app ⟨·⟩) ≫ (Pi.isoLimit _).hom := by
      apply limit.hom_ext
      intro ⟨n⟩
      simp
    rw [this]
    infer_instance

end Limits

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- An abelian category with countable products in which sequential limits of epimorphisms
project epimorphically onto the first term satisfies countable AB4\*. -/
lemma CountableAB4Star.of_epi_π_app_zero [Abelian C] [HasCountableProducts C]
    (h : EpiπAppZeroOfEpi C) : CountableAB4Star C :=
  have := lim_preservesEpimorphisms_of_epi_π_app_zero h
  have := hasExactLimitsOfShape_of_preservesEpi C (Discrete ℕ)
  CountableAB4Star.of_hasExactLimitsOfShape_nat _

end CategoryTheory
