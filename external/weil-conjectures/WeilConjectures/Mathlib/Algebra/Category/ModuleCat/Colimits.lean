/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Elements outside the range of a map of colimits

An element which stays outside the range of a map at every stage of a cofiltered system stays
outside the range of the induced map of colimits.
-/

@[expose] public section

namespace ModuleCat

open CategoryTheory

/-- An element of a module which survives at every stage of a cofiltered system survives at the
limit, when the sources of the comparison maps form a filtered colimit up to surjectivity and the
targets are a filtered colimit up to injectivity. -/
lemma notMem_range_of_forall_notMem_range
    {R : Type*} [Ring R] {I : Type*} [Category I]
    [IsCofiltered I] (A B : I → ModuleCat R) (Al Bl B₀ : ModuleCat R) (φ : ∀ i, A i ⟶ B i)
    (φl : Al ⟶ Bl) (tA : ∀ {i j : I}, (j ⟶ i) → (A i ⟶ A j))
    (tB : ∀ {i j : I}, (j ⟶ i) → (B i ⟶ B j))
    (sA : ∀ i, A i ⟶ Al) (sB : ∀ i, B i ⟶ Bl) (τ : ∀ i, B₀ ⟶ B i) (τl : B₀ ⟶ Bl)
    (hτ : ∀ {i j : I} (f : j ⟶ i), τ i ≫ tB f = τ j) (hτl : ∀ i, τ i ≫ sB i = τl)
    (hφ : ∀ {i j : I} (f : j ⟶ i), φ i ≫ tB f = tA f ≫ φ j)
    (hφl : ∀ i, φ i ≫ sB i = sA i ≫ φl) (hsA : ∀ {i j : I} (f : j ⟶ i), tA f ≫ sA j = sA i)
    (hA : ∀ y : Al, y ∈ ⨆ i, LinearMap.range (sA i).hom)
    (hB : ∀ (i : I) (b : B i), (sB i).hom b = 0 → ∃ (j : I) (f : j ⟶ i), (tB f).hom b = 0)
    (ξ : B₀) (hξ : ∀ i, (τ i).hom ξ ∉ Set.range (φ i).hom) :
    (τl).hom ξ ∉ Set.range φl.hom := by
  rintro ⟨η, hη⟩
  have key : ∀ y ∈ ⨆ i, LinearMap.range (sA i).hom, ∃ i y', (sA i).hom y' = y := by
    intro y hy
    induction hy using Submodule.iSup_induction' with
    | mem i y hy => obtain ⟨y', rfl⟩ := hy; exact ⟨i, y', rfl⟩
    | zero => exact ⟨IsCofiltered.nonempty.some, 0, map_zero _⟩
    | add y z _ _ hy hz =>
      obtain ⟨i, y', rfl⟩ := hy
      obtain ⟨j, z', rfl⟩ := hz
      refine ⟨IsCofiltered.min i j, (tA (IsCofiltered.minToLeft i j)).hom y' +
        (tA (IsCofiltered.minToRight i j)).hom z', ?_⟩
      rw [map_add, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply, hsA, hsA]
  obtain ⟨i, η', rfl⟩ := key η (hA η)
  have h0 : (sB i).hom ((φ i).hom η' - (τ i).hom ξ) = 0 := by
    rw [map_sub, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply, hφl, hτl, ModuleCat.comp_apply,
      hη, sub_self]
  obtain ⟨j, f, hf⟩ := hB i _ h0
  apply hξ j
  refine ⟨(tA f).hom η', ?_⟩
  rw [map_sub, sub_eq_zero] at hf
  rw [← ModuleCat.comp_apply, ← hφ, ModuleCat.comp_apply, hf, ← ModuleCat.comp_apply, hτ]

end ModuleCat
