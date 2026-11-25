/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.Restriction
public import WeilConjectures.AlgebraicGeometry.Modules.FreeMatrix
public import WeilConjectures.AlgebraicGeometry.Modules.HomSection

/-!
# Complexes of free modules given by matrices

For finite index types `ι n` and matrices `D n` of global functions on a scheme `Y` with
`D (n + 1) * D n = 0`, `AlgebraicGeometry.Scheme.Modules.freeComplex D hD` is the cochain complex
of `𝒪_Y`-modules with terms `𝒪_Y^{(ι n)}` and differentials the morphisms with matrices `D n`.

* Its pullback along `j : Z ⟶ Y` is the complex of the images of the matrices
  (`AlgebraicGeometry.Scheme.Modules.pullbackFreeComplexIso`).
* A morphism from it (restricted to nonnegative degrees) to a complex `K` of `𝒪_Y`-modules indexed
  by `ℕ` is given by global sections of the terms of `K` satisfying the relations of the matrices
  (`AlgebraicGeometry.Scheme.Modules.freeComplexHom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {Y : Scheme.{u}}

/-! ### Morphisms out of free modules given by sections -/

/-- The morphism `𝒪_Y^{(I)} ⟶ M` sending the `i`-th basis vector to the global section `c i`. -/
noncomputable def freeHomOfSections (M : Y.Modules) {I : Type u} [Fintype I] [DecidableEq I]
    (c : I → Γ(M, ⊤)) : free (R := Y.ringCatSheaf) I ⟶ M :=
  ∑ i, freeπ i ≫ homOfGlobalSection M (c i)

@[reassoc (attr := simp)]
lemma ιFree_freeHomOfSections (M : Y.Modules) {I : Type u} [Fintype I] [DecidableEq I]
    (c : I → Γ(M, ⊤)) (i : I) :
    ιFree i ≫ freeHomOfSections M c = homOfGlobalSection M (c i) := by
  rw [freeHomOfSections, Preadditive.comp_sum, Finset.sum_eq_single i]
  · rw [ιFree_freeπ_assoc, ite_eq_left rfl, Category.id_comp]
  · intro j _ hj
    rw [ιFree_freeπ_assoc, ite_eq_right (Ne.symm hj), zero_comp]
  · simp

/-- The sections over `W` of `freeHomOfSections M c`: `x ↦ ∑ᵢ xᵢ • (c i)|_W`. -/
lemma freeHomOfSections_app (M : Y.Modules) {I : Type u} [Fintype I] [DecidableEq I]
    (c : I → Γ(M, ⊤)) (W : Y.Opens) (x : Γ(free (R := Y.ringCatSheaf) I, W)) :
    Hom.app (freeHomOfSections M c) W x =
      ∑ i, freeSectionsEquivOpens W I x i • M.presheaf.map (homOfLE le_top).op (c i) := by
  rw [freeHomOfSections, Hom.sum_app_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Hom.comp_app, ConcreteCategory.comp_apply, homOfGlobalSection_app]
  rfl

/-- The `i`-th column of a matrix, as a composite of the inclusion of the `i`-th summand. -/
@[reassoc]
lemma ιFree_freeHomOfMatrix {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix J I Γ(Y, ⊤)) (i : I) :
    ιFree i ≫ freeHomOfMatrix A = ∑ j, (Modules.unit Y).smulHom (A j i) ≫ ιFree j := by
  rw [freeHomOfMatrix, Preadditive.comp_sum, Finset.sum_eq_single i]
  · rw [Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [ιFree_freeπ_assoc, ite_eq_left rfl, Category.id_comp]
  · intro i' _ hi
    rw [Preadditive.comp_sum]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [ιFree_freeπ_assoc, ite_eq_right (Ne.symm hi), zero_comp]
  · simp

lemma homOfGlobalSection_app_top_one (M : Y.Modules) (u : Γ(M, ⊤)) :
    (homOfGlobalSection M u).app ⊤ (1 : Γ(Y, ⊤)) = u := by
  rw [homOfGlobalSection_app_one, presheaf_map_id_apply]

/-! ### The complex -/

variable {ι : ℤ → Type u} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]

/-- **The complex of free modules with differentials given by matrices**: in degree `n` it is
`𝒪_Y^{(ι n)}`, with differential `𝒪_Y^{(ι n)} ⟶ 𝒪_Y^{(ι (n + 1))}` of matrix `D n`. -/
noncomputable def freeComplex (D : ∀ n : ℤ, Matrix (ι (n + 1)) (ι n) Γ(Y, ⊤))
    (hD : ∀ n, D (n + 1) * D n = 0) : CochainComplex Y.Modules ℤ :=
  CochainComplex.of (fun n ↦ free (R := Y.ringCatSheaf) (ι n)) (fun n ↦ freeHomOfMatrix (D n))
    (fun n ↦ freeMatrix_injective (by
      rw [freeMatrix_comp, freeMatrix_freeHomOfMatrix, freeMatrix_freeHomOfMatrix, hD,
        freeMatrix_zero]))

variable (D : ∀ n : ℤ, Matrix (ι (n + 1)) (ι n) Γ(Y, ⊤)) (hD : ∀ n, D (n + 1) * D n = 0)

lemma freeComplex_X (n : ℤ) : (freeComplex D hD).X n = free (R := Y.ringCatSheaf) (ι n) :=
  rfl

lemma freeComplex_d (n : ℤ) : (freeComplex D hD).d n (n + 1) = freeHomOfMatrix (D n) :=
  CochainComplex.of_d (fun n ↦ free (R := Y.ringCatSheaf) (ι n)) (fun n ↦ freeHomOfMatrix (D n)) n

lemma freeComplex_d_natCast (k : ℕ) :
    (freeComplex D hD).d k (k + 1 : ℕ) = freeHomOfMatrix (D k) :=
  freeComplex_d D hD k

omit [∀ n, DecidableEq (ι n)] in
include hD in
lemma map_appTop_mul_eq_zero {Z : Scheme.{u}} (j : Z ⟶ Y) (n : ℤ) :
    (D (n + 1)).map j.appTop.hom * (D n).map j.appTop.hom = 0 := by
  rw [← Matrix.map_mul, hD n, Matrix.map_zero _ (map_zero _)]

/-- **The pullback of a complex of free modules given by matrices** is the complex of free
modules given by the images of the matrices. -/
noncomputable def pullbackFreeComplexIso {Z : Scheme.{u}} (j : Z ⟶ Y) :
    ((pullback j).mapHomologicalComplex _).obj (freeComplex D hD) ≅
      freeComplex (fun n ↦ (D n).map j.appTop.hom) (map_appTop_mul_eq_zero D hD j) :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ pullbackFreeIso j (ι n)) (by
    rintro n _ rfl
    have h : (pullbackFreeIso j (ι n)).inv ≫ (pullback j).map (freeHomOfMatrix (D n)) ≫
        (pullbackFreeIso j (ι (n + 1))).hom = freeHomOfMatrix ((D n).map j.appTop.hom) :=
      freeMatrix_injective (by
        rw [freeMatrix_pullback, freeMatrix_freeHomOfMatrix, freeMatrix_freeHomOfMatrix])
    rw [Functor.mapHomologicalComplex_obj_d, freeComplex_d, freeComplex_d, ← h,
      Iso.hom_inv_id_assoc])

/-! ### Morphisms to complexes indexed by `ℕ` -/

/-- **A morphism from a complex of free modules to a complex indexed by `ℕ`**, given by global
sections `c k i` of the terms of `K` (the images of the basis vectors) satisfying
`d (c k i) = ∑ⱼ D k j i • c (k + 1) j`. -/
noncomputable def freeComplexHom (K : CochainComplex Y.Modules ℕ)
    (c : ∀ k : ℕ, ι k → Γ(K.X k, ⊤))
    (hc : ∀ (k : ℕ) (i : ι k), (K.d k (k + 1)).app ⊤ (c k i) =
      ∑ j : ι ((k : ℤ) + 1), D k j i • c (k + 1) j) :
    (freeComplex D hD).restriction ComplexShape.embeddingUpNat ⟶ K where
  f k := freeHomOfSections (K.X k) (c k)
  comm' := by
    rintro k _ rfl
    have h : ((freeComplex D hD).restriction ComplexShape.embeddingUpNat).d k (k + 1) =
        freeHomOfMatrix (D k) := freeComplex_d_natCast D hD k
    rw [h]
    symm
    refine free_hom_ext fun i ↦ unit_hom_ext ?_
    rw [ιFree_freeHomOfSections_assoc, ιFree_freeHomOfMatrix_assoc, Preadditive.sum_comp,
      Hom.sum_app_apply, Hom.comp_app (homOfGlobalSection _ _), ConcreteCategory.comp_apply,
      homOfGlobalSection_app_top_one, hc]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Category.assoc, ιFree_freeHomOfSections, Hom.comp_app, ConcreteCategory.comp_apply,
      smulHom_app_apply, homOfGlobalSection_app, presheaf_map_id_apply]
    rw [smul_eq_mul, mul_one, Scheme.presheaf_map_id_apply]

lemma freeComplexHom_f (K : CochainComplex Y.Modules ℕ) (c : ∀ k : ℕ, ι k → Γ(K.X k, ⊤))
    (hc : ∀ (k : ℕ) (i : ι k), (K.d k (k + 1)).app ⊤ (c k i) =
      ∑ j : ι ((k : ℤ) + 1), D k j i • c (k + 1) j) (k : ℕ) :
    (freeComplexHom D hD K c hc).f k = freeHomOfSections (K.X k) (c k) :=
  rfl

end AlgebraicGeometry.Scheme.Modules
