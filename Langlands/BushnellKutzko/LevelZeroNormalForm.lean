import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.PEquiv
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Tactic.NoncommRing

/-! # The rank normal form with the identity block in the first coordinates -/

open Matrix

noncomputable section

namespace Langlands.BushnellKutzko.LevelZero

universe uR

/-- The diagonal matrix with `1` in the first `r` diagonal positions and `0` elsewhere. -/
def erMat (R : Type uR) [Zero R] [One R] {f : ℕ} (r : ℕ) : Matrix (Fin f) (Fin f) R :=
  Matrix.diagonal fun a => if a.val < r then 1 else 0

theorem erMat_apply (R : Type uR) [Zero R] [One R] {f : ℕ} (r : ℕ) (a b : Fin f) :
    erMat R r a b = if a = b ∧ a.val < r then 1 else 0 := by
  by_cases hab : a = b
  · subst hab; simp [erMat, Matrix.diagonal_apply_eq]
  · simp [erMat, hab]

theorem map_erMat {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S) {f : ℕ} (r : ℕ) :
    (erMat R (f := f) r).map φ = erMat S r := by
  ext a b
  simp only [Matrix.map_apply, erMat_apply]
  split_ifs <;> simp

/-- Every nonzero singular square matrix over a field is `P * erMat r * Q` with `P, Q`
invertible and `0 < r < f`. -/
theorem exists_erMat_form {k : Type uR} [Field k] {f : ℕ} (X : Matrix (Fin f) (Fin f) k)
    (h0 : X ≠ 0) (hu : ¬ IsUnit X) :
    ∃ r : ℕ, 0 < r ∧ r < f ∧ ∃ P Q : GL (Fin f) k,
      (P : Matrix (Fin f) (Fin f) k) * erMat k r * (Q : Matrix (Fin f) (Fin f) k) = X := by
  classical
  obtain ⟨V, U, e, hV, hU, hX⟩ := Matrix.exists_rank_normal_form X
  generalize hs : Fintype.card (Fin f) - X.rank = s at e hX
  generalize hr : X.rank = r at e hX hs
  have hcard : f = r + s := by
    have := Fintype.card_congr e
    simpa using this
  -- the normal form as a diagonal matrix
  have hD : (fromBlocks (1 : Matrix (Fin r) (Fin r) k) 0 0 (0 : Matrix (Fin s) (Fin s) k)).submatrix
      e e = Matrix.diagonal fun a => (Sum.elim (fun _ => (1 : k)) (fun _ => 0)) (e a) := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_zero, Matrix.fromBlocks_diagonal,
      Matrix.submatrix_diagonal_equiv]
    rfl
  let σ : Fin f ≃ Fin f := e.trans (finSumFinEquiv.trans (finCongr hcard.symm))
  have hσ : ∀ a, ((σ a).val < r ↔ (e a).isLeft) := by
    intro a
    simp only [σ, Equiv.trans_apply, finCongr_apply, Fin.val_cast]
    rcases e a with x | y
    · simp [finSumFinEquiv_apply_left]
    · simp [finSumFinEquiv_apply_right]
  have hDer : Matrix.diagonal (fun a => (Sum.elim (fun _ => (1 : k)) (fun _ => 0)) (e a)) =
      (erMat k r).submatrix σ σ := by
    rw [erMat, Matrix.submatrix_diagonal_equiv]
    congr 1
    funext a
    have := hσ a
    rcases ha : e a with x | y
    · rw [ha] at this; simp at this; simp [this]
    · rw [ha] at this; simp at this; simp [not_lt.mpr this]
  have hperm : (erMat k r).submatrix σ σ =
      σ.toPEquiv.toMatrix * erMat k r * σ.symm.toPEquiv.toMatrix := by
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    simp
  have hVX : V * X * U = σ.toPEquiv.toMatrix * erMat k r * σ.symm.toPEquiv.toMatrix := by
    rw [hX, hD, hDer, hperm]
  let A : Matrix (Fin f) (Fin f) k := ((hV.unit⁻¹ : (Matrix (Fin f) (Fin f) k)ˣ) :
    Matrix (Fin f) (Fin f) k)
  let B : Matrix (Fin f) (Fin f) k := ((hU.unit⁻¹ : (Matrix (Fin f) (Fin f) k)ˣ) :
    Matrix (Fin f) (Fin f) k)
  have hA : A * V = 1 := hV.val_inv_mul
  have hB : U * B = 1 := hU.mul_val_inv
  have key : ∀ Y : Matrix (Fin f) (Fin f) k, A * (V * Y * U) * B = Y := by
    intro Y
    calc A * (V * Y * U) * B = (A * V) * Y * (U * B) := by noncomm_ring
      _ = Y := by rw [hA, hB, one_mul, mul_one]
  have hr0 : 0 < r := by
    by_contra hr0
    have hr' : r = 0 := by omega
    apply h0
    have : V * X * U = 0 := by
      rw [hX, hD]
      ext a b
      rcases ha : e a with x | y
      · exact absurd x.2 (by omega)
      · simp [Matrix.diagonal_apply, ha]
    rw [← key X, this]; simp
  have hrf : r < f := by
    by_contra hrf
    have hs' : s = 0 := by omega
    apply hu
    have hone : V * X * U = 1 := by
      rw [hX, hD]
      ext a b
      rcases ha : e a with x | y
      · simp [Matrix.diagonal_apply, ha, Matrix.one_apply]
      · exact absurd y.2 (by omega)
    rw [← key X, hone, mul_one]
    exact (hV.unit⁻¹ * hU.unit⁻¹).isUnit
  let Pσ : GL (Fin f) k := ⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix, by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp, by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp⟩
  refine ⟨r, hr0, hrf, hV.unit⁻¹ * Pσ, Pσ⁻¹ * hU.unit⁻¹, ?_⟩
  have hPσ : (Pσ : Matrix (Fin f) (Fin f) k) = σ.toPEquiv.toMatrix := rfl
  have hPσinv : ((Pσ⁻¹ : GL (Fin f) k) : Matrix (Fin f) (Fin f) k) =
      σ.symm.toPEquiv.toMatrix := rfl
  simp only [Units.val_mul, hPσ, hPσinv]
  calc A * σ.toPEquiv.toMatrix * erMat k r * (σ.symm.toPEquiv.toMatrix * B)
      = A * (σ.toPEquiv.toMatrix * erMat k r * σ.symm.toPEquiv.toMatrix) * B := by noncomm_ring
    _ = A * (V * X * U) * B := by rw [hVX]
    _ = X := key X

end Langlands.BushnellKutzko.LevelZero
