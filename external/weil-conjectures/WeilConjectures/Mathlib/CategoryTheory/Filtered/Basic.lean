/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Data.Fintype.Basic

/-!
# Finitely many properties at a common stage of a cofiltered category

If finitely many properties of morphisms `k ⟶ j` into a fixed object `j` of a cofiltered category
each hold for some morphism and are stable under precomposition, then they all hold for a common
morphism (`CategoryTheory.IsCofiltered.exists_forall_of_finite`). A finite family of objects has a
common lower bound (`CategoryTheory.IsCofiltered.exists_forall_nonempty_hom`). Dually, finite
families of objects and of morphisms out of an object of a filtered category have cocones
(`CategoryTheory.IsFiltered.exists_cocone_of_finite`,
`CategoryTheory.IsFiltered.exists_comp_eq_of_finite`).
-/

@[expose] public section

namespace CategoryTheory.IsCofiltered

variable {C : Type*} [Category* C] [IsCofiltered C]

/-- Finitely many properties of morphisms into `j`, each of which holds for some morphism into `j`
and is stable under precomposition, hold simultaneously for some morphism into `j`. -/
theorem exists_forall_of_finite {ι : Type*} [Finite ι] {j : C}
    (P : ι → ∀ {k : C}, (k ⟶ j) → Prop)
    (hP : ∀ i {k k' : C} (u : k' ⟶ k) (t : k ⟶ j), P i t → P i (u ≫ t))
    (h : ∀ i, ∃ (k : C) (t : k ⟶ j), P i t) : ∃ (k : C) (t : k ⟶ j), ∀ i, P i t := by
  classical
  have := Fintype.ofFinite ι
  suffices H : ∀ s : Finset ι, ∃ (k : C) (t : k ⟶ j), ∀ i ∈ s, P i t by
    obtain ⟨k, t, hk⟩ := H Finset.univ
    exact ⟨k, t, fun i ↦ hk i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨j, 𝟙 j, by simp⟩
  | insert i s _ ih =>
    obtain ⟨k₁, t₁, h₁⟩ := ih
    obtain ⟨k₂, t₂, h₂⟩ := h i
    let a := minToLeft k₁ k₂ ≫ t₁
    let b := minToRight k₁ k₂ ≫ t₂
    refine ⟨eq a b, eqHom a b ≫ a, fun i' hi' ↦ ?_⟩
    rcases Finset.mem_insert.mp hi' with rfl | hi'
    · rw [eq_condition]
      simpa only [b, Category.assoc] using hP i' (eqHom a b ≫ minToRight k₁ k₂) t₂ h₂
    · simpa only [a, Category.assoc] using hP i' (eqHom a b ≫ minToLeft k₁ k₂) t₁ (h₁ i' hi')

/-- A finite family of objects of a cofiltered category has a common lower bound. -/
lemma exists_forall_nonempty_hom {K : Type*} [Finite K] (F : K → C) :
    ∃ l : C, ∀ k, Nonempty (l ⟶ F k) := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨l, hl⟩ := inf_objs_exists (Finset.univ.image F)
  exact ⟨l, fun k ↦ hl (Finset.mem_image_of_mem F (Finset.mem_univ k))⟩

end CategoryTheory.IsCofiltered

namespace CategoryTheory.IsFiltered

variable {K : Type*} [Category* K]

/-- A finite family of morphisms `aᵢ : k ⟶ kᵢ` out of an object of a filtered category extends to
a cocone: there are `A : k ⟶ k'` and `bᵢ : kᵢ ⟶ k'` with `aᵢ ≫ bᵢ = A`. -/
lemma exists_comp_eq_of_finite [IsFilteredOrEmpty K] {k : K}
    {ι : Type*} [Finite ι] {k₁ : ι → K} (a : ∀ i, k ⟶ k₁ i) :
    ∃ (k' : K) (A : k ⟶ k') (b : ∀ i, k₁ i ⟶ k'), ∀ i, a i ≫ b i = A := by
  classical
  have := Fintype.ofFinite ι
  have : Nonempty K := ⟨k⟩
  have : IsFiltered K := { }
  let O : Finset K := insert k (Finset.univ.image k₁)
  have hk : k ∈ O := Finset.mem_insert_self _ _
  have hk₁ (i : ι) : k₁ i ∈ O :=
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  let H : Finset (Σ' (X Y : K) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) :=
    Finset.univ.image fun i ↦ ⟨k, k₁ i, hk, hk₁ i, a i⟩
  exact ⟨IsFiltered.sup O H, IsFiltered.toSup O H hk, fun i ↦ IsFiltered.toSup O H (hk₁ i),
    fun i ↦ IsFiltered.toSup_commutes O H hk (hk₁ i)
      (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩

/-- A finite family of objects of a filtered category has a cocone. -/
lemma exists_cocone_of_finite [IsFiltered K] {ι : Type*} [Finite ι]
    (k₁ : ι → K) : ∃ k : K, Nonempty (∀ i, k₁ i ⟶ k) := by
  classical
  have := Fintype.ofFinite ι
  let O : Finset K := Finset.univ.image k₁
  exact ⟨IsFiltered.sup O ∅, ⟨fun i ↦ IsFiltered.toSup O ∅
    (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩⟩

end CategoryTheory.IsFiltered
