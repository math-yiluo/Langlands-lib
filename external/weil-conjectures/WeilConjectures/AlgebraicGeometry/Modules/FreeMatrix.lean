/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplexExact

/-!
# Morphisms of free modules of finite rank are matrices

For finite index types `I` and `J`, morphisms `𝒪_Y^{(I)} ⟶ 𝒪_Y^{(J)}` of free `𝒪_Y`-modules are
the same as `J × I` matrices of global functions on `Y`: the matrix `freeMatrix φ` determines `φ`
(`AlgebraicGeometry.Scheme.Modules.freeMatrix_injective`), every matrix is the matrix of the
morphism `freeHomOfMatrix A` (`AlgebraicGeometry.Scheme.Modules.freeMatrix_freeHomOfMatrix`), and
composition, identities and sums correspond to products, identity matrices and sums of matrices.
-/

@[expose] public section

universe u

open CategoryTheory Limits SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {Y : Scheme.{u}}

/-- The global function by which an endomorphism of `𝒪_Y` multiplies: its value at `1`. -/
noncomputable def unitValue (a : Modules.unit Y ⟶ Modules.unit Y) : Γ(Y, ⊤) :=
  Hom.app a ⊤ (1 : Γ(Y, ⊤))

/-- The value at `1` of a composite of endomorphisms of `𝒪_Y` is the product of the values. -/
lemma unitValue_comp (a b : Modules.unit Y ⟶ Modules.unit Y) :
    unitValue (a ≫ b) = unitValue a * unitValue b := by
  unfold unitValue
  rw [Hom.comp_app, ConcreteCategory.comp_apply, unit_hom_app_top]
  rfl

lemma freeMatrix_apply {I J : Type u} [DecidableEq J]
    (φ : free (R := Y.ringCatSheaf) I ⟶ free J) (j : J) (i : I) :
    freeMatrix φ j i = unitValue (ιFree i ≫ φ ≫ freeπ j) :=
  rfl

lemma unitValue_sum {ι : Type*} (s : Finset ι) (a : ι → (Modules.unit Y ⟶ Modules.unit Y)) :
    unitValue (∑ i ∈ s, a i) = ∑ i ∈ s, unitValue (a i) :=
  Hom.sum_app_apply s a ⊤ _

/-- The matrix of a composite is the product of the matrices. -/
lemma freeMatrix_comp {I J K : Type u} [Fintype J] [DecidableEq J] [DecidableEq K]
    (φ : free (R := Y.ringCatSheaf) I ⟶ free J) (ψ : free (R := Y.ringCatSheaf) J ⟶ free K) :
    freeMatrix (φ ≫ ψ) = freeMatrix ψ * freeMatrix φ := by
  ext k i
  have h : ιFree i ≫ (φ ≫ ψ) ≫ freeπ k =
      ∑ j, (ιFree i ≫ φ ≫ freeπ j) ≫ (ιFree j ≫ ψ ≫ freeπ k) := by
    calc ιFree i ≫ (φ ≫ ψ) ≫ freeπ k =
        ιFree i ≫ φ ≫ (∑ j, freeπ j ≫ ιFree j) ≫ ψ ≫ freeπ k := by
          rw [sum_freeπ_ιFree, Category.id_comp, Category.assoc]
      _ = _ := by simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
  rw [Matrix.mul_apply, freeMatrix_apply, h, unitValue_sum]
  exact Finset.sum_congr rfl fun j _ ↦ (unitValue_comp _ _).trans (mul_comm _ _)

@[simp]
lemma unitValue_id : unitValue (𝟙 (Modules.unit Y)) = 1 :=
  rfl

@[simp]
lemma unitValue_zero : unitValue (0 : Modules.unit Y ⟶ Modules.unit Y) = 0 :=
  rfl

lemma unitValue_add (a b : Modules.unit Y ⟶ Modules.unit Y) :
    unitValue (a + b) = unitValue a + unitValue b :=
  rfl

lemma unitValue_sub (a b : Modules.unit Y ⟶ Modules.unit Y) :
    unitValue (a - b) = unitValue a - unitValue b :=
  rfl


@[simp]
lemma unitValue_smulHom (a : Γ(Y, ⊤)) : unitValue ((Modules.unit Y).smulHom a) = a := by
  unfold unitValue
  rw [smulHom_app_apply, Subsingleton.elim (homOfLE le_top) (𝟙 (⊤ : Y.Opens)), op_id,
    CategoryTheory.Functor.map_id]
  exact mul_one a

/-- The matrix of the identity is the identity matrix. -/
@[simp]
lemma freeMatrix_id {I : Type u} [DecidableEq I] :
    freeMatrix (𝟙 (free (R := Y.ringCatSheaf) I)) = 1 := by
  ext j i
  rw [freeMatrix_apply, Category.id_comp, ιFree_freeπ, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl]
    exact unitValue_id
  · simp [h, Ne.symm h]

/-- The matrix of a sum is the sum of the matrices. -/
lemma freeMatrix_add {I J : Type u} [DecidableEq J] (φ ψ : free (R := Y.ringCatSheaf) I ⟶ free J) :
    freeMatrix (φ + ψ) = freeMatrix φ + freeMatrix ψ := by
  ext j i
  rw [freeMatrix_apply, Preadditive.add_comp, Preadditive.comp_add, unitValue_add]
  rfl

/-- The matrix of a difference is the difference of the matrices. -/
lemma freeMatrix_sub {I J : Type u} [DecidableEq J] (φ ψ : free (R := Y.ringCatSheaf) I ⟶ free J) :
    freeMatrix (φ - ψ) = freeMatrix φ - freeMatrix ψ := by
  ext j i
  rw [freeMatrix_apply, Preadditive.sub_comp, Preadditive.comp_sub, unitValue_sub]
  rfl


/-- A morphism of free modules of finite rank is determined by its matrix. -/
lemma freeMatrix_injective {I J : Type u} [Finite I] [Finite J] [DecidableEq J] :
    Function.Injective
      (freeMatrix : (free (R := Y.ringCatSheaf) I ⟶ free J) → Matrix J I Γ(Y, ⊤)) := by
  classical
  have := Fintype.ofFinite I
  have := Fintype.ofFinite J
  intro φ ψ h
  refine hom_ext _ _ fun W ↦ ?_
  ext x
  apply (freeSectionsEquivOpens W J).injective
  rw [freeSectionsEquivOpens_app, freeSectionsEquivOpens_app, h]

/-- The morphism of free modules of finite rank with a given matrix. -/
noncomputable def freeHomOfMatrix {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix J I Γ(Y, ⊤)) : free (R := Y.ringCatSheaf) I ⟶ free J :=
  ∑ i, ∑ j, freeπ i ≫ (Modules.unit Y).smulHom (A j i) ≫ ιFree j

@[simp]
lemma freeMatrix_freeHomOfMatrix {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (A : Matrix J I Γ(Y, ⊤)) : freeMatrix (freeHomOfMatrix A) = A := by
  ext j i
  rw [freeMatrix_apply, freeHomOfMatrix]
  simp_rw [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
  rw [unitValue_sum, Finset.sum_eq_single i, unitValue_sum, Finset.sum_eq_single j]
  · rw [ιFree_freeπ_assoc, ite_eq_left rfl, Category.id_comp, ιFree_freeπ, ite_eq_left rfl,
      Category.comp_id, unitValue_smulHom]
  · intro j' _ hj
    rw [ιFree_freeπ, ite_eq_right hj, comp_zero, comp_zero, comp_zero, unitValue_zero]
  · simp
  · intro i' _ hi
    rw [unitValue_sum]
    refine Finset.sum_eq_zero fun j' _ ↦ ?_
    rw [ιFree_freeπ_assoc, ite_eq_right (Ne.symm hi), zero_comp, unitValue_zero]
  · simp

/-- Every morphism of free modules of finite rank is the morphism of its matrix. -/
@[simp]
lemma freeHomOfMatrix_freeMatrix {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (φ : free (R := Y.ringCatSheaf) I ⟶ free J) :
    freeHomOfMatrix (freeMatrix φ) = φ :=
  freeMatrix_injective (freeMatrix_freeHomOfMatrix _)

end AlgebraicGeometry.Scheme.Modules
