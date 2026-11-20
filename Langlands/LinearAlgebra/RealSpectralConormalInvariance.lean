import Langlands.LinearAlgebra.MatrixOrbitTangentDeterminant
import Langlands.LinearAlgebra.RealSpectralNormalAction

/-! # Transpose invariance of continuous functions on the normal dual -/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 4

namespace Langlands

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation:max "T[" A "]" => LinearMap.range (matrixConjugationTangent A)
local notation:max "Z[" A "]" => realMatrixSemisimpleDirections A
local notation:max "S[" A "]" => (T[A] ⊔ Z[A])
local notation:max "C[" A "]" => matrixConormalWith A Z[A]
local notation:max "conjL[" u "]" => LinearEquiv.toContinuousLinearEquiv (matrixConjugationLinearEquiv u)
local notation:max "transposeL[" q "]" => LinearEquiv.toContinuousLinearEquiv (matrixAdjustedTransposeLinearEquiv q)

variable {A : Matrix (Fin n) (Fin n) ℝ}

theorem matrixConjugation_fixes_realMatrixSemisimpleDirections {u : Matˣ}
    (hu : Commute (u : Mat) A) {z : Mat} (hz : z ∈ Z[A]) :
    matrixConjugationLinearEquiv u z = z := by
  apply add_left_cancel (a := A)
  have hA : matrixConjugationLinearEquiv u A = A := by
    change u.val * A * u.inv = A
    rw [hu.eq, mul_assoc, u.val_inv, mul_one]
  have h := conjugate_add_semisimpleDirection_eq hu hz
  change matrixConjugationLinearEquiv u (A + z) = A + z at h
  rwa [map_add, hA] at h

theorem matrixAdjustedTranspose_fixes_realMatrixSemisimpleDirections {q : Matˣ}
    (hq : q.val * A * q.inv = Aᵀ) {z : Mat} (hz : z ∈ Z[A]) :
    matrixAdjustedTransposeLinearEquiv q z = z := by
  apply add_left_cancel (a := A)
  have hA : matrixAdjustedTransposeLinearEquiv q A = A := by
    change q.inv * Aᵀ * q.val = A
    rw [← hq]
    simp [mul_assoc]
  have h := adjustedTranspose_add_semisimpleDirection_eq hq hz
  change matrixAdjustedTransposeLinearEquiv q (A + z) = A + z at h
  rwa [map_add, hA] at h

/-- Normal action from ambient conjugation by a unit. It is the quotient action when the unit
stabilizes the base matrix. -/
def realMatrixStratumStabilizerNormalAction
    {W : Submodule ℝ Mat} {N : Submodule ℝ W}
    (hZW : Z[A] ≤ W) (hTW : IsCompl T[A] W) (hN : IsCompl (Z[A].comap W.subtype) N)
    (u : Matˣ) : N →L[ℝ] N :=
  realMatrixStratumNormalAction hZW hTW hN conjL[u]

/-- Normal action from transpose followed by conjugation by the inverse of a unit. It is the
quotient action when the unit carries the base matrix to its transpose. -/
def realMatrixStratumAdjustedTransposeNormalAction
    {W : Submodule ℝ Mat} {N : Submodule ℝ W}
    (hZW : Z[A] ≤ W) (hTW : IsCompl T[A] W) (hN : IsCompl (Z[A].comap W.subtype) N)
    (q : Matˣ) : N →L[ℝ] N :=
  realMatrixStratumNormalAction hZW hTW hN transposeL[q]

/-- A continuous function of normal covectors invariant under precomposition by all the
stabilizer actions is also invariant under precomposition by adjusted transpose. -/
theorem realMatrixStratumNormalDual_transpose_invariant
    {W : Submodule ℝ Mat} {N : Submodule ℝ W}
    (hZW : Z[A] ≤ W) (hTW : IsCompl T[A] W) (hN : IsCompl (Z[A].comap W.subtype) N)
    {E : Type*} [TopologicalSpace E] [T2Space E] (f : (N →L[ℝ] ℝ) → E) (hf : Continuous f)
    (hconj : ∀ (u : Matˣ), Commute (u : Mat) A → ∀ covector : N →L[ℝ] ℝ,
      f (covector.comp (realMatrixStratumStabilizerNormalAction hZW hTW hN u)) = f covector)
    {q : Matˣ} (hq : q.val * A * q.inv = Aᵀ) (covector : N →L[ℝ] ℝ) :
    f (covector.comp (realMatrixStratumAdjustedTransposeNormalAction hZW hTW hN q)) = f covector := by
  let P := realMatrixTraceNormalFunctional W N
  let F : Mat → E := fun X => f (P X)
  have hF : Continuous F := hf.comp P.continuous_of_finiteDimensional
  let σ : Mat ≃L[ℝ] Mat := transposeL[q]
  have hσB (X Y : Mat) : matrixTraceBilin (σ X) (σ Y) = matrixTraceBilin X Y :=
    (matrixTraceBilin_units_conj q⁻¹ Xᵀ Yᵀ).trans (matrixTraceBilin_transpose X Y)
  have hσT : T[A] ≤ T[A].comap σ.toContinuousLinearMap.toLinearMap := by
    apply matrixOrbitTangent_invariant_of_intertwines A _ (c := -1) (by simp)
    intro X
    rw [neg_one_smul]
    exact matrixConjugationTangent_adjustedTranspose hq X
  have hσS (X : Mat) (hX : X ∈ S[A]) : σ X ∈ S[A] := by
    obtain ⟨t, ht, z, hz, rfl⟩ := Submodule.mem_sup.mp hX
    rw [map_add]
    have hz' : σ z = z := matrixAdjustedTranspose_fixes_realMatrixSemisimpleDirections hq hz
    rw [hz']
    exact Submodule.mem_sup.mpr ⟨σ t, hσT ht, z, hz, rfl⟩
  have hσC (X : Mat) (hX : X ∈ C[A]) : σ.symm X ∈ C[A] := by
    intro Y hY
    change matrixTraceBilin Y (σ.symm X) = 0
    have h := hσB Y (σ.symm X)
    rw [σ.apply_symm_apply] at h
    exact h.symm.trans (hX _ (hσS Y hY))
  have hclosed : IsClosed {p : Mat × Mat | F p.1 = F p.2} :=
    isClosed_eq (hF.comp continuous_fst) (hF.comp continuous_snd)
  have hσF (X : Mat) (hX : X ∈ C[A]) : F X = F (σ X) := by
    apply (closure_minimal ?_ hclosed) (mem_closure_conormalConjugacy_of_semisimplePart hq hX)
    rintro ⟨Y, Y'⟩ ⟨hY, u, hu, hEq⟩
    change u.val * Y * u.inv = Y' at hEq
    subst Y'
    have huB (V V' : Mat) : matrixTraceBilin (conjL[u⁻¹] V) (conjL[u⁻¹] V') =
        matrixTraceBilin V V' := matrixTraceBilin_units_conj u⁻¹ V V'
    have he := realMatrixTraceNormalFunctional_comp hZW hTW hN conjL[u⁻¹] huB hY
    have hinv (V : Mat) : conjL[u⁻¹].symm V = u.val * V * u.inv := by
      change (matrixConjugationLinearEquiv u⁻¹).symm V = _
      rw [matrixConjugationLinearEquiv_symm, inv_inv, matrixConjugationLinearEquiv_apply]
    rw [hinv] at he
    change f (P Y) = f (P (u.val * Y * u.inv))
    rw [← he]
    exact (hconj u⁻¹ hu.units_inv_left (P Y)).symm
  obtain ⟨X, hCovector⟩ := (realMatrixStratumConormalEquiv hZW hTW hN).surjective covector
  rw [realMatrixStratumConormalEquiv_apply] at hCovector
  rw [realMatrixStratumAdjustedTransposeNormalAction, ← hCovector]
  change f ((P X).comp (realMatrixStratumNormalAction hZW hTW hN σ)) = f (P X)
  rw [realMatrixTraceNormalFunctional_comp hZW hTW hN σ hσB X.property]
  have h := hσF (σ.symm X.val) (hσC X.val X.property)
  rwa [σ.apply_symm_apply] at h

end Langlands
