/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import WeilConjectures.CategoryTheory.Triangulated.DerivedAdicComplete

/-!
# Criteria for derived adic completeness

We collect some elementary criteria for derived `n`-adic completeness
(`CategoryTheory.IsDerivedAdicComplete`) of an object of a preadditive category.

## Main statements

- `CategoryTheory.IsDerivedAdicComplete.of_isZero`: zero objects are derived complete.
- `CategoryTheory.IsDerivedAdicComplete.of_map`: if a family of additive functors preserving the
  product `∏_{i : ℕ} K` jointly reflects isomorphisms, and sends `K` to derived complete
  objects, then `K` is derived complete.
- `CategoryTheory.IsDerivedAdicComplete.biproduct`: finite biproducts of derived complete
  objects are derived complete.
- `AddCommGrpCat.isDerivedAdicComplete_iff_bijective`: an abelian group `G` is derived
  `n`-adically complete if and only if `(xᵢ) ↦ (xᵢ - n • xᵢ₊₁)` is a bijection of `ℕ → G`.

-/

@[expose] public section

namespace CategoryTheory

open Limits Category Preadditive

universe w v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]

namespace IsDerivedAdicComplete

/-- A zero object is derived `n`-adically complete. -/
lemma of_isZero {n : ℤ} {K : C} [HasProduct (fun _ : ℕ ↦ K)] (hK : IsZero K) :
    IsDerivedAdicComplete n K := by
  have hP : IsZero (∏ᶜ fun _ : ℕ ↦ K) :=
    (IsZero.iff_id_eq_zero _).2 (Pi.hom_ext _ _ fun _ ↦ hK.eq_of_tgt _ _)
  exact ⟨0, hP.eq_of_src _ _, hP.eq_of_src _ _⟩

/-- If a family of additive functors `Fᵢ` preserving the product `∏_{j : ℕ} K` jointly reflects
isomorphisms and each `Fᵢ K` is derived `n`-adically complete, then so is `K`: the image of
`𝟙 - n • adicTowerShift K` under `Fᵢ` is conjugate to `𝟙 - n • adicTowerShift (Fᵢ K)`. -/
lemma of_map {ι : Type*} {D : ι → Type u₂} [∀ i, Category.{v₂} (D i)] [∀ i, Preadditive (D i)]
    (F : ∀ i, C ⥤ D i) [∀ i, (F i).Additive] {n : ℤ} {K : C} [HasProduct (fun _ : ℕ ↦ K)]
    [∀ i, HasProduct (fun _ : ℕ ↦ (F i).obj K)]
    [∀ i, PreservesLimit (Discrete.functor fun _ : ℕ ↦ K) (F i)]
    (hF : ∀ {X Y : C} (f : X ⟶ Y), (∀ i, IsIso ((F i).map f)) → IsIso f)
    (hK : ∀ i, IsDerivedAdicComplete n ((F i).obj K)) : IsDerivedAdicComplete n K := by
  refine hF _ fun i ↦ ?_
  have : IsIso (𝟙 _ - n • adicTowerShift ((F i).obj K)) := hK i
  rw [(IsIso.eq_comp_inv _).2 (map_one_sub_zsmul_adicTowerShift_comp_piComparison (F i) n K)]
  infer_instance

section Biproduct

variable {J : Type} [Finite J] (K : J → C) [HasBiproduct K]
  [∀ j, HasProduct fun _ : ℕ ↦ K j] [HasProduct fun _ : ℕ ↦ ⨁ K]
  [HasBiproduct fun j ↦ ∏ᶜ fun _ : ℕ ↦ K j]

/-- The comparison `∏_{i : ℕ} ⨁_j K_j ⟶ ⨁_j ∏_{i : ℕ} K_j`. -/
noncomputable def piBiproductComparison :
    (∏ᶜ fun _ : ℕ ↦ ⨁ K) ⟶ ⨁ fun j ↦ ∏ᶜ fun _ : ℕ ↦ K j :=
  biproduct.lift fun j ↦ Limits.Pi.map fun _ ↦ biproduct.π K j

/-- The comparison `∏_{i : ℕ} ⨁_j K_j ⟶ ⨁_j ∏_{i : ℕ} K_j` is an isomorphism. -/
instance isIso_piBiproductComparison : IsIso (piBiproductComparison K) := by
  classical
  have := Fintype.ofFinite J
  refine ⟨biproduct.desc fun j ↦ Limits.Pi.map fun _ ↦ biproduct.ι K j, ?_, ?_⟩
  · refine Pi.hom_ext _ _ fun i ↦ ?_
    rw [piBiproductComparison, biproduct.lift_desc, sum_comp, id_comp]
    simp only [assoc, Limits.Pi.map_π,
      Limits.Pi.map_π_assoc]
    rw [← comp_sum, biproduct.total, comp_id]
  · refine biproduct.hom_ext' _ _ fun j ↦ biproduct.hom_ext _ _ fun j' ↦ ?_
    rw [piBiproductComparison, biproduct.ι_desc_assoc, assoc, biproduct.lift_π, comp_id]
    by_cases h : j = j'
    · subst h
      refine Pi.hom_ext _ _ fun i ↦ ?_
      simp
    · refine Pi.hom_ext _ _ fun i ↦ ?_
      simp [biproduct.ι_π_ne _ h]

/-- Finite biproducts of derived `n`-adically complete objects are derived `n`-adically
complete. -/
lemma biproduct {n : ℤ} (hK : ∀ j, IsDerivedAdicComplete n (K j)) :
    IsDerivedAdicComplete n (⨁ K) := by
  have : ∀ j, IsIso (𝟙 _ - n • adicTowerShift (K j)) := hK
  have h : (𝟙 _ - n • adicTowerShift (⨁ K)) ≫ piBiproductComparison K =
      piBiproductComparison K ≫
        (biproduct.mapIso fun j ↦ asIso (𝟙 _ - n • adicTowerShift (K j))).hom := by
    refine biproduct.hom_ext _ _ fun j ↦ ?_
    simp only [piBiproductComparison, assoc, biproduct.lift_π, biproduct.mapIso_hom,
      biproduct.map_π, asIso_hom, biproduct.lift_π_assoc]
    exact (pi_map_comp_one_sub_zsmul_adicTowerShift n (biproduct.π K j)).symm
  rw [IsDerivedAdicComplete, (IsIso.eq_comp_inv _).2 h]
  infer_instance

end Biproduct

end IsDerivedAdicComplete

end CategoryTheory

namespace AddCommGrpCat

open CategoryTheory Category Limits Preadditive

universe w

/-- An abelian group `G` is derived `n`-adically complete if and only if the map
`(xᵢ) ↦ (xᵢ - n • xᵢ₊₁)` is a bijection of `ℕ → G`. -/
lemma isDerivedAdicComplete_iff_bijective (n : ℤ) (G : AddCommGrpCat.{w}) :
    IsDerivedAdicComplete n G ↔
      Function.Bijective fun x : ℕ → G ↦ fun i ↦ x i - n • x (i + 1) := by
  let e := Concrete.productEquiv (fun _ : ℕ ↦ G)
  have h : (fun x : ℕ → G ↦ fun i ↦ x i - n • x (i + 1)) =
      e ∘ ⇑(𝟙 (∏ᶜ fun _ : ℕ ↦ G) - n • adicTowerShift G) ∘ e.symm := by
    funext x i
    simp only [Function.comp_apply, e, Concrete.productEquiv_apply_apply]
    rw [← ConcreteCategory.comp_apply, sub_comp, zsmul_comp, adicTowerShift_π, id_comp]
    simp [Concrete.productEquiv_symm_apply_π]
  rw [IsDerivedAdicComplete, ConcreteCategory.isIso_iff_bijective, h, e.comp_bijective,
    e.symm.bijective_comp]

end AddCommGrpCat
