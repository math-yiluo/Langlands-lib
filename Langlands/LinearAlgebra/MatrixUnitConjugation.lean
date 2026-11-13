import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Matrix.Basis

/-! # Systems of matrix units in a full matrix algebra are conjugate to the standard one -/

namespace Langlands.LinearAlgebra.MatrixUnitConjugation

open Matrix

variable {F : Type*} [Field F] {m : Type*} [Fintype m] [DecidableEq m]

/-- The square matrix whose `j`-th column is `E j p *ᵥ v`. For a system of matrix units `E`
and a nonzero vector `v` fixed by `E p p`, it conjugates the standard matrix units to `E`. -/
def unitColumnMatrix (E : m → m → Matrix m m F) (p : m) (v : m → F) : Matrix m m F :=
  Matrix.of fun r j => (E j p *ᵥ v) r

/-- If the matrices `E i j` satisfy the matrix-unit relations
`E i j * E k l = δ_{jk} E i l` and one `E p p` is nonzero, then there is an invertible
matrix `P` with `P * single i j 1 = E i j * P` for all `i j`. -/
theorem exists_mul_single_eq (E : m → m → Matrix m m F)
    (hE : ∀ i j k l, E i j * E k l = if j = k then E i l else 0)
    (p : m) (hp : E p p ≠ 0) :
    ∃ P : GL m F, ∀ i j, (P : Matrix m m F) * single i j 1 = E i j * (P : Matrix m m F) := by
  obtain ⟨w, hw⟩ : ∃ w : m → F, E p p *ᵥ w ≠ 0 := by
    by_contra h
    push Not at h
    apply hp
    ext r k
    have := congrFun (h (Pi.single k 1)) r
    simpa [mulVec_single_one] using this
  set v := E p p *ᵥ w with hvdef
  have hv : E p p *ᵥ v = v := by
    rw [hvdef, mulVec_mulVec, hE, ite_eq_left rfl]
  have hEv : ∀ i j k, E i j *ᵥ (E k p *ᵥ v) = if j = k then E i p *ᵥ v else 0 := by
    intro i j k
    rw [mulVec_mulVec, hE]
    split_ifs <;> simp
  let P : Matrix m m F := unitColumnMatrix E p v
  have hPcol : ∀ (A : Matrix m m F) r k, (A * P) r k = (A *ᵥ (E k p *ᵥ v)) r := by
    intro A r k
    simp [P, unitColumnMatrix, mul_apply, mulVec, dotProduct]
  have hcomm : ∀ i j, P * single i j 1 = E i j * P := by
    intro i j
    ext r k
    rw [hPcol, hEv]
    by_cases hjk : j = k
    · subst hjk
      simp [P, unitColumnMatrix]
    · rw [ite_eq_right hjk, mul_single_apply_of_ne (hbj := Ne.symm hjk)]
      rfl
  have hinj : ∀ c : m → F, P *ᵥ c = 0 → c = 0 := by
    intro c hc
    ext k
    have hPc : P *ᵥ c = ∑ j, c j • (E j p *ᵥ v) := by
      ext r
      simp [P, unitColumnMatrix, mulVec, dotProduct, Finset.sum_apply, mul_comm]
    have h1 : E p k *ᵥ (P *ᵥ c) = c k • v := by
      rw [hPc, mulVec_sum]
      simp_rw [mulVec_smul, hEv]
      rw [Finset.sum_eq_single k]
      · rw [ite_eq_left rfl, hv]
      · intro j _ hjk
        rw [ite_eq_right (Ne.symm hjk), smul_zero]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    rw [hc, mulVec_zero] at h1
    have hv0 : v ≠ 0 := hw
    by_contra hck
    apply hv0
    have := congrArg (fun x => (c k)⁻¹ • x) h1
    simpa [smul_smul, inv_mul_cancel₀ hck] using this.symm
  have hdet : P.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    exact hc0 (hinj c hc)
  have hunit : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).mpr (IsUnit.mk0 _ hdet)
  exact ⟨hunit.unit, fun i j => by rw [IsUnit.unit_spec]; exact hcomm i j⟩

end Langlands.LinearAlgebra.MatrixUnitConjugation
