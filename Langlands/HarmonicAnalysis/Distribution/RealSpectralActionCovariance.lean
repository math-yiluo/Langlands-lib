import Langlands.HarmonicAnalysis.Distribution.RealMatrixJacobian
import Langlands.LinearAlgebra.RealSpectralConormalInvariance

/-! # Signed ambient covariance and normal determinants for real spectral charts -/

noncomputable section

open scoped Distributions Matrix Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.HarmonicAnalysis.RealGeneralLinearDistribution

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation:max "T[" A "]" => LinearMap.range (matrixConjugationTangent A)

/-- Transpose followed by conjugation by the inverse matrix, as a continuous
linear equivalence on the full real matrix space. -/
abbrev fullAdjustedTransposeEquiv (q : Matˣ) : Mat ≃L[ℝ] Mat :=
  (matrixAdjustedTransposeLinearEquiv q).toContinuousLinearEquiv

/-- The adjusted transpose has unit absolute determinant. -/
theorem abs_det_fullAdjustedTransposeEquiv (q : Matˣ) :
    |(fullAdjustedTransposeEquiv q).toContinuousLinearMap.det| = 1 := by
  have hc := det_fullConjugationEquiv q⁻¹
  change LinearMap.det (matrixConjugationLinearEquiv q⁻¹).toLinearMap = 1 at hc
  change |LinearMap.det ((matrixConjugationLinearEquiv q⁻¹).toLinearMap.comp
    (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ).toLinearMap)| = 1
  rw [LinearMap.det_comp, hc, one_mul]
  exact abs_det_fullTransposeEquiv (n := n)

/-- A conjugation-invariant distribution odd under transpose retains that sign
for transpose followed by the inverse conjugation. -/
theorem eval_fullSmoothTestPullbackCLM_fullAdjustedTranspose
    (D : FullDistribution n) (hconj : IsFullConjugationInvariant D)
    (htranspose : IsFullTransposeAntiInvariant D) (q : Matˣ) (f : FullTest n) :
    D (fullSmoothTestPullbackCLM (fullAdjustedTransposeEquiv q) f) = -D f := by
  have hp : fullSmoothTestPullbackCLM (fullAdjustedTransposeEquiv q) f =
      fullTransposeTest (fullConjugationTest q⁻¹ f) := by
    ext X
    rw [fullSmoothTestPullbackCLM_apply, fullTransposeTest_apply, fullConjugationTest_apply]
    rfl
  rw [hp, htranspose, hconj]

variable {A : Matrix (Fin n) (Fin n) ℝ} {W : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)}
  {N : Submodule ℝ W}
  (hZW : realMatrixSemisimpleDirections A ≤ W)
  (hTW : IsCompl (LinearMap.range (matrixConjugationTangent A)) W)
  (hN : IsCompl ((realMatrixSemisimpleDirections A).comap W.subtype) N)

theorem fullConjugationEquiv_preserves_tangent {u : Matˣ} (hu : Commute (u : Mat) A) :
    T[A] ≤ T[A].comap (fullConjugationEquiv u).toLinearEquiv.toLinearMap := by
  apply matrixOrbitTangent_invariant_of_intertwines A _ (c := 1) (by simp)
  intro X
  rw [one_smul]
  exact matrixConjugationTangent_conjugation hu X

theorem fullAdjustedTransposeEquiv_preserves_tangent {q : Matˣ}
    (hq : q.val * A * q.inv = Aᵀ) :
    T[A] ≤ T[A].comap (fullAdjustedTransposeEquiv q).toLinearEquiv.toLinearMap := by
  apply matrixOrbitTangent_invariant_of_intertwines A _ (c := -1) (by simp)
  intro X
  rw [neg_one_smul]
  exact matrixConjugationTangent_adjustedTranspose hq X

/-- Conjugation by a stabilizer of the center has unit absolute determinant on
the normal quotient. -/
theorem abs_det_realMatrixStratumStabilizerNormalAction {u : Matˣ} (hu : Commute (u : Mat) A) :
    |LinearMap.det (M := ↥N) (realMatrixStratumStabilizerNormalAction hZW hTW hN u).toLinearMap| =
      (1 : ℝ) := by
  have ht := fullConjugationEquiv_preserves_tangent hu
  exact abs_det_realMatrixStratumNormalAction hZW hTW hN (fullConjugationEquiv u) ht
    (fun _ hz => matrixConjugation_fixes_realMatrixSemisimpleDirections hu hz)
    (by
      change |(fullConjugationEquiv u).toContinuousLinearMap.det| = 1
      rw [det_fullConjugationEquiv, abs_one])
    (abs_det_matrixConjugationOrbitTangent hu ht)

/-- Adjusted transpose fixing the center has unit absolute determinant on the
normal quotient. -/
theorem abs_det_realMatrixStratumAdjustedTransposeNormalAction {q : Matˣ}
    (hq : q.val * A * q.inv = Aᵀ) :
    |LinearMap.det (M := ↥N) (realMatrixStratumAdjustedTransposeNormalAction hZW hTW hN q).toLinearMap| =
      (1 : ℝ) := by
  have ht := fullAdjustedTransposeEquiv_preserves_tangent hq
  exact abs_det_realMatrixStratumNormalAction hZW hTW hN (fullAdjustedTransposeEquiv q) ht
    (fun _ hz => matrixAdjustedTranspose_fixes_realMatrixSemisimpleDirections hq hz)
    (abs_det_fullAdjustedTransposeEquiv q) (abs_det_matrixAdjustedTransposeOrbitTangent hq ht)

end Langlands.HarmonicAnalysis.RealGeneralLinearDistribution
