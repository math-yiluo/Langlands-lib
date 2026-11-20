import Langlands.HarmonicAnalysis.Distribution.RealMatrixTransposeOdd
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Trace

/-! # Determinants and infinitesimal trace on real matrix space -/

noncomputable section

open scoped Matrix Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis.RealGeneralLinearDistribution

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "GL" => Langlands.GeneralLinear n ℝ

/-- The ambient commutator field for a fixed matrix, regarded as a continuous
linear endomorphism of real matrix space. -/
def commutatorVectorCLM (X : Mat) : Mat →L[ℝ] Mat :=
  (LinearMap.mulLeft ℝ X - LinearMap.mulRight ℝ X).toContinuousLinearMap

@[simp]
theorem commutatorVectorCLM_apply (X A : Mat) :
    commutatorVectorCLM X A = X * A - A * X := rfl

theorem trace_commutatorVectorCLM (X : Mat) :
    LinearMap.trace ℝ Mat (commutatorVectorCLM X).toLinearMap = 0 := by
  let e : (Fin n → Fin n → ℝ) ≃ₗ[ℝ] Mat := Matrix.ofLinearEquiv ℝ
  let b : Module.Basis (Σ _ : Fin n, Fin n) ℝ Mat :=
    (Pi.basis (fun _ : Fin n => Pi.basisFun ℝ (Fin n))).map e
  have hb (ij : Σ _ : Fin n, Fin n) : b ij = Matrix.single ij.1 ij.2 1 := by
    rcases ij with ⟨k, l⟩
    rw [show b ⟨k, l⟩ = e (Pi.basis (fun _ : Fin n => Pi.basisFun ℝ (Fin n)) ⟨k, l⟩)
      from Module.Basis.map_apply _ _ _, Pi.basis_apply, Pi.basisFun_apply]
    ext i j
    by_cases h : k = i
    · subst i
      simp [e, Matrix.single_apply, Pi.single_apply, eq_comm]
    · simp [e, eq_comm, h]
  have hrepr (A : Mat) (ij : Σ _ : Fin n, Fin n) : b.repr A ij = A ij.1 ij.2 := by
    change (Pi.basisFun ℝ (Fin n)).repr (A ij.1) ij.2 = _
    simp
  rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
  have hdiag (ij : Σ _ : Fin n, Fin n) :
      ((LinearMap.toMatrix b b) (commutatorVectorCLM X).toLinearMap).diag ij =
        X ij.1 ij.1 - X ij.2 ij.2 := by
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hrepr, hb]
    simp
  simp_rw [hdiag, Finset.sum_sub_distrib, Fintype.sum_sigma]
  rw [Finset.sum_comm (f := fun i j : Fin n => X i i)]
  simp

private theorem det_matrixMulRight (A : Mat) :
    LinearMap.det (LinearMap.mulRight ℝ A) = A.det ^ n := by
  let L := Matrix.toLin' Aᵀ
  let e : (Fin n → Fin n → ℝ) ≃ₗ[ℝ] Mat := Matrix.ofLinearEquiv ℝ
  have heq : LinearMap.mulRight ℝ A =
      e.toLinearMap ∘ₗ LinearMap.pi (fun i : Fin n => L.comp (LinearMap.proj i)) ∘ₗ
        e.symm.toLinearMap := by
    ext1 B
    ext i j
    change (B * A) i j = (Aᵀ *ᵥ B i) j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  rw [heq, LinearMap.det_conj, LinearMap.det_pi]
  simp [L]

private theorem det_matrixMulLeft (A : Mat) :
    LinearMap.det (LinearMap.mulLeft ℝ A) = A.det ^ n := by
  let e := Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ
  have heq : LinearMap.mulLeft ℝ A =
      e.toLinearMap ∘ₗ LinearMap.mulRight ℝ Aᵀ ∘ₗ e.symm.toLinearMap := by
    ext1 B
    change A * B = (Bᵀ * Aᵀ)ᵀ
    simp
  rw [heq, LinearMap.det_conj, det_matrixMulRight, Matrix.det_transpose]

/-- Inner conjugation has determinant one on the space of all real matrices. -/
theorem det_fullConjugationEquiv (g : GL) :
    (fullConjugationEquiv g).toContinuousLinearMap.det = 1 := by
  change LinearMap.det ((LinearMap.mulRight ℝ (↑(g⁻¹) : Mat)).comp
    (LinearMap.mulLeft ℝ (g : Mat))) = 1
  rw [LinearMap.det_comp, det_matrixMulRight, det_matrixMulLeft, ← mul_pow, ← Matrix.det_mul]
  simp

/-- Transpose has unit absolute determinant on real matrix space. -/
theorem abs_det_fullTransposeEquiv :
    |(fullTransposeEquiv n).toContinuousLinearMap.det| = 1 := by
  let L := (fullTransposeEquiv n).toContinuousLinearMap.toLinearMap
  have hL : L.comp L = LinearMap.id := by
    ext1 A
    exact Matrix.transpose_transpose A
  change |LinearMap.det L| = 1
  rw [← abs_one, ← sq_eq_sq_iff_abs_eq_abs, sq, ← LinearMap.det_comp, hL]
  simp

end Langlands.HarmonicAnalysis.RealGeneralLinearDistribution
