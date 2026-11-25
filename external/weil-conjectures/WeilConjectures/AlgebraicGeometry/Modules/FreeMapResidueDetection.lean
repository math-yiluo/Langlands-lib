/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator

/-! # Residue fields detect maps between finite free sheaves on reduced schemes -/

@[expose] public section

universe u

open CategoryTheory Limits SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

private theorem unit_map_eq_zero_of_top_one {X : Scheme.{u}} {N : X.Modules}
    (σ : Modules.unit X ⟶ N) (h : σ.app ⊤ (1 : Γ(X, ⊤)) = 0) : σ = 0 := by
  refine hom_ext _ _ fun U ↦ ?_
  ext r
  obtain ⟨a, rfl⟩ :=
    ((isFreeGenerator_one (X := X) ⊤).map (le_top : U ≤ ⊤)).exists_smul_eq r
  rw [Hom.app_smul]
  erw [Hom.app_presheaf_map σ (homOfLE (le_top : U ≤ ⊤)) (1 : Γ(X, ⊤))]
  erw [h]
  simp

/-- Residue-field evaluations detect a morphism between finite free sheaves on a reduced scheme. -/
theorem free_map_eq_zero_of_residue_evaluations
    {X : Scheme.{u}} [IsReduced X] {I J : Type u} [Finite J] [DecidableEq J]
    (δ : free (R := X.ringCatSheaf) I ⟶ free J)
    (hδ : ∀ x : X, (freeMatrix δ).map (X.Γevaluation x) = 0) : δ = 0 := by
  let := Fintype.ofFinite J
  have hentries : ∀ j i, freeMatrix δ j i = 0 := by
    intro j i
    apply eq_zero_of_basicOpen_eq_bot
    apply (X.basicOpen_eq_bot_iff_forall_evaluation_eq_zero _).mpr
    intro x
    exact congrFun (congrFun (hδ x.1) j) i
  apply free_hom_ext
  intro i
  have hcoord : ∀ j : J, ιFree i ≫ δ ≫ freeπ j = 0 := by
    intro j
    apply unit_map_eq_zero_of_top_one
    exact hentries j i
  calc
    ιFree i ≫ δ = (ιFree i ≫ δ) ≫ 𝟙 _ := by simp
    _ = (ιFree i ≫ δ) ≫ ∑ j : J, freeπ j ≫ ιFree j := by rw [sum_freeπ_ιFree]
    _ = 0 := by
      rw [Preadditive.comp_sum]
      apply Finset.sum_eq_zero
      intro j _
      have hj : (ιFree i ≫ δ) ≫ freeπ j = 0 := by
        simpa only [Category.assoc] using hcoord j
      rw [← Category.assoc, hj, zero_comp]
    _ = ιFree i ≫ 0 := by simp

end AlgebraicGeometry.Scheme.Modules
