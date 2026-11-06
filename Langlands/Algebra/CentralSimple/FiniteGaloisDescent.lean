import Mathlib.Data.Matrix.Basic
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Finite Galois descent of matrix splitting charts -/

noncomputable section

universe u

namespace Langlands.CentralSimple

open scoped TensorProduct

variable {K E A : Type u} [Field K] [Field E] [Ring A]
  [Algebra K E] [Algebra K A]
variable {d : ℕ}

/-- Restrict a matrix representation when all its entries lie in an
intermediate field. -/
def restrictMatrixEntries
    (f : A →ₐ[K] Matrix (Fin d) (Fin d) E)
    (L : IntermediateField K E) (hf : ∀ a i j, f a i j ∈ L) :
    A →ₐ[K] Matrix (Fin d) (Fin d) L where
  toFun a i j := ⟨f a i j, hf a i j⟩
  map_zero' := by
    ext i j
    exact congrFun (congrFun f.map_zero i) j
  map_one' := by
    ext i j
    simp [Matrix.one_apply, apply_ite]
  map_add' a b := by
    ext i j
    exact congrFun (congrFun (f.map_add a b) i) j
  map_mul' a b := by
    ext i j
    change f (a * b) i j =
      ((∑ k, (⟨f a i k, hf a i k⟩ : L) * ⟨f b k j, hf b k j⟩ : L) : E)
    simp [Matrix.mul_apply]
  commutes' k := by
    ext i j
    by_cases h : i = j <;>
      simp [Algebra.algebraMap_eq_smul_one, h]

@[simp]
theorem restrictMatrixEntries_coe
    (f : A →ₐ[K] Matrix (Fin d) (Fin d) E)
    (L : IntermediateField K E) (hf : ∀ a i j, f a i j ∈ L)
    (a : A) (i j : Fin d) :
    ((restrictMatrixEntries f L hf a i j : L) : E) = f a i j := rfl

/-- Any matrix chart after a field extension fixes the dimension over the
original field. -/
theorem finrank_eq_matrixSize
    (e : E ⊗[K] A ≃ₐ[E] Matrix (Fin d) (Fin d) E) :
    Module.finrank K A = d * d := by
  have h := e.toLinearEquiv.finrank_eq
  simpa [Module.finrank_baseChange, Module.finrank_matrix] using h

/-- The original algebra's representation attached to a scalar-extension
matrix chart. -/
def matrixChartRepresentation
    (e : E ⊗[K] A ≃ₐ[E] Matrix (Fin d) (Fin d) E) :
    A →ₐ[K] Matrix (Fin d) (Fin d) E :=
  (e.toAlgHom.restrictScalars K).comp Algebra.TensorProduct.includeRight

@[simp]
theorem matrixChartRepresentation_apply
    (e : E ⊗[K] A ≃ₐ[E] Matrix (Fin d) (Fin d) E) (a : A) :
    matrixChartRepresentation e a = e (1 ⊗ₜ[K] a) := rfl

/-- Extend the restricted representation to the intermediate field. -/
def restrictedMatrixChartHom
    (e : E ⊗[K] A ≃ₐ[E] Matrix (Fin d) (Fin d) E)
    (L : IntermediateField K E)
    (hf : ∀ a i j, matrixChartRepresentation e a i j ∈ L) :
    L ⊗[K] A →ₐ[L] Matrix (Fin d) (Fin d) L :=
  AlgHom.liftEquiv K L A _ (restrictMatrixEntries (matrixChartRepresentation e) L hf)

/-- After including entries into the ambient field, the restricted map agrees
with the original chart and the tensor inclusion. -/
theorem restrictedMatrixChartHom_coe
    (e : E ⊗[K] A ≃ₐ[E] Matrix (Fin d) (Fin d) E)
    (L : IntermediateField K E)
    (hf : ∀ a i j, matrixChartRepresentation e a i j ∈ L)
    (x : L ⊗[K] A) :
    (restrictedMatrixChartHom e L hf x).map ((↑) : L → E) =
      e (TensorProduct.map L.val.toLinearMap (LinearMap.id : A →ₗ[K] A) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul l a =>
      ext i j
      simp only [restrictedMatrixChartHom, AlgHom.liftEquiv_tmul,
        TensorProduct.map_tmul, LinearMap.id_apply]
      change (l : E) * e (1 ⊗ₜ[K] a) i j = e ((l : E) ⊗ₜ[K] a) i j
      have h : (l : E) ⊗ₜ[K] a = (l : E) • (1 ⊗ₜ[K] a) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h, map_smul]
      rfl
  | add x y hx hy =>
      ext i j
      have hxi := congrFun (congrFun hx i) j
      have hyi := congrFun (congrFun hy i) j
      simpa [Matrix.map_apply] using congrArg₂ (· + ·) hxi hyi

theorem restrictedMatrixChartHom_injective
    (e : E ⊗[K] A ≃ₐ[E] Matrix (Fin d) (Fin d) E)
    (L : IntermediateField K E)
    (hf : ∀ a i j, matrixChartRepresentation e a i j ∈ L) :
    Function.Injective (restrictedMatrixChartHom e L hf) := by
  have ht := TensorProduct.map_injective_of_flat_flat L.val.toLinearMap
    (LinearMap.id : A →ₗ[K] A) Subtype.val_injective Function.injective_id
  intro x y h
  apply ht
  apply e.injective
  rw [← restrictedMatrixChartHom_coe e L hf x,
    ← restrictedMatrixChartHom_coe e L hf y, h]

/-- A chart whose coefficients lie in an intermediate field descends to that
field. -/
def restrictedMatrixChart [FiniteDimensional K A]
    (e : E ⊗[K] A ≃ₐ[E] Matrix (Fin d) (Fin d) E)
    (L : IntermediateField K E)
    (hf : ∀ a i j, matrixChartRepresentation e a i j ∈ L) :
    L ⊗[K] A ≃ₐ[L] Matrix (Fin d) (Fin d) L :=
  AlgEquiv.ofBijective (restrictedMatrixChartHom e L hf) ⟨
    restrictedMatrixChartHom_injective e L hf,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simpa [Module.finrank_baseChange, Module.finrank_matrix] using
        finrank_eq_matrixSize e)).mp (restrictedMatrixChartHom_injective e L hf)⟩

/-- Matrix entries of the images of a finite basis of the original algebra. -/
def matrixChartCoefficients [FiniteDimensional K A]
    (e : E ⊗[K] A ≃ₐ[E] Matrix (Fin d) (Fin d) E) : Set E :=
  Set.range fun p : Fin (Module.finrank K A) × Fin d × Fin d =>
    matrixChartRepresentation e (Module.finBasis K A p.1) p.2.1 p.2.2

instance matrixChartCoefficients_finite [FiniteDimensional K A]
    (e : E ⊗[K] A ≃ₐ[E] Matrix (Fin d) (Fin d) E) :
    Finite (matrixChartCoefficients e) := by
  dsimp [matrixChartCoefficients]
  infer_instance

/-- The finite Galois intermediate field generated by all basis-image entries
of the given matrix chart. -/
def finiteGaloisMatrixChartField [FiniteDimensional K A] [IsGalois K E]
    (e : E ⊗[K] A ≃ₐ[E] Matrix (Fin d) (Fin d) E) :
    FiniteGaloisIntermediateField K E :=
  FiniteGaloisIntermediateField.adjoin K (matrixChartCoefficients e)

theorem matrixChartRepresentation_mem_finiteGaloisField
    [FiniteDimensional K A] [IsGalois K E]
    (e : E ⊗[K] A ≃ₐ[E] Matrix (Fin d) (Fin d) E)
    (a : A) (i j : Fin d) :
    matrixChartRepresentation e a i j ∈
      (finiteGaloisMatrixChartField e).toIntermediateField := by
  let b := Module.finBasis K A
  have h : matrixChartRepresentation e a i j =
      ∑ k, b.repr a k • matrixChartRepresentation e (b k) i j := by
    conv_lhs => rw [← b.sum_repr a]
    simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply]
  rw [h]
  apply IntermediateField.sum_mem
  intro k _
  apply IntermediateField.smul_mem
  exact FiniteGaloisIntermediateField.subset_adjoin K (matrixChartCoefficients e)
    ⟨(k, i, j), rfl⟩

/-- Descend a chart over a possibly infinite Galois extension to the finite
Galois intermediate field generated by its basis-image entries. -/
def finiteGaloisMatrixChart [FiniteDimensional K A] [IsGalois K E]
    (e : E ⊗[K] A ≃ₐ[E] Matrix (Fin d) (Fin d) E) :
    (finiteGaloisMatrixChartField e).toIntermediateField ⊗[K] A ≃ₐ[
      (finiteGaloisMatrixChartField e).toIntermediateField]
      Matrix (Fin d) (Fin d) (finiteGaloisMatrixChartField e).toIntermediateField :=
  restrictedMatrixChart e (finiteGaloisMatrixChartField e).toIntermediateField
    (matrixChartRepresentation_mem_finiteGaloisField e)

theorem exists_finiteGalois_matrix_chart [FiniteDimensional K A] [IsGalois K E]
    (e : E ⊗[K] A ≃ₐ[E] Matrix (Fin d) (Fin d) E) :
    ∃ L : FiniteGaloisIntermediateField K E,
      Nonempty (L.toIntermediateField ⊗[K] A ≃ₐ[L.toIntermediateField]
        Matrix (Fin d) (Fin d) L.toIntermediateField) :=
  ⟨finiteGaloisMatrixChartField e, ⟨finiteGaloisMatrixChart e⟩⟩

end Langlands.CentralSimple
