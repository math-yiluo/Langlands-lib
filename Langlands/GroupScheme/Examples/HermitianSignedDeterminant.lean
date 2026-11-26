import Langlands.GroupScheme.Examples.HermitianMatrixDeterminant
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! # Signed determinants of Hermitian Gram matrices -/

noncomputable section

universe u v w

namespace Langlands.GroupScheme.HermitianRoot.MultiHyperbolic

variable {A : Type u} [CommRing A] {α : Type v} {β : Type w}
  [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

private def endpointsAndMiddle : β ⊕ (α × Bool) ≃ Index α β where
  toFun
    | .inl i => .inr (.inl i)
    | .inr (i, false) => .inl i
    | .inr (i, true) => .inr (.inr i)
  invFun
    | .inl i => .inr (i, false)
    | .inr (.inl i) => .inl i
    | .inr (.inr i) => .inr (i, true)
  left_inv
    | .inl _ | .inr (_, false) | .inr (_, true) => rfl
  right_inv
    | .inl _ | .inr (.inl _) | .inr (.inr _) => rfl

/-- Each hyperbolic plane contributes a factor of `-1` to the determinant. -/
theorem det_gram (M : Matrix β β A) :
    (gram (α := α) M).det = (-1) ^ Fintype.card α * M.det := by
  let e : β ⊕ (α × Bool) ≃ Index α β := endpointsAndMiddle
  let s : Equiv.Perm (α × Bool) := Equiv.prodCongrRight (fun _ => Equiv.swap false true)
  have he : (gram (α := α) M).submatrix e e = Matrix.fromBlocks M 0 0 (s.permMatrix A) := by
    ext i j
    rcases i with i | ⟨i, bi⟩ <;> rcases j with j | ⟨j, bj⟩
    all_goals try cases bi
    all_goals try cases bj
    all_goals simp [gram, e, endpointsAndMiddle, s, Equiv.prodCongrRight_apply,
      PEquiv.toMatrix_apply]
  rw [← Matrix.det_submatrix_equiv_self e, he, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_permutation]
  have hs : Equiv.Perm.sign s = (-1) ^ Fintype.card α := by
    dsimp only [s]
    rw [Equiv.Perm.sign_prodCongrRight]
    simp
  rw [hs]
  push_cast
  exact mul_comm _ _

end Langlands.GroupScheme.HermitianRoot.MultiHyperbolic

namespace Langlands.GroupScheme.HermitianMatrix.Form

open SU3Root

variable {L : Type u} [Field L] {c : RingInvolution L} {n : ℕ}

/-- The signed determinant uses one factor of `-1` per pair of coordinates. -/
def signedDeterminant (H : Form c (Fin n)) : L :=
  (-1) ^ (n / 2) * (H.gram : Matrix (Fin n) (Fin n) L).det

theorem signedDeterminant_ne_zero (H : Form c (Fin n)) : H.signedDeterminant ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (Matrix.GeneralLinearGroup.det_ne_zero H.gram)

theorem bar_signedDeterminant (H : Form c (Fin n)) :
    c.bar H.signedDeterminant = H.signedDeterminant := by
  rw [signedDeterminant, map_mul, map_pow, map_neg, map_one, ← det_adjoint, H.hermitian]

/-- A binary Hermitian Gram matrix with signed determinant in the norm image
has a nonzero isotropic vector. -/
theorem exists_isotropic_of_signedDeterminant (H : Form c (Fin 2)) {b : L}
    (hb : c.bar b * b = H.signedDeterminant) :
    ∃ x : Fin 2 → L, x ≠ 0 ∧ H.linearFirst x x = 0 := by
  let G : Matrix (Fin 2) (Fin 2) L := H.gram
  have hfix (i j : Fin 2) : c.bar (G j i) = G i j :=
    congrArg (fun X : Matrix (Fin 2) (Fin 2) L => X i j) H.hermitian
  have hdet : c.bar b * b = -(G 0 0 * G 1 1 - G 0 1 * G 1 0) := by
    simpa [signedDeterminant, G, Matrix.det_fin_two] using hb
  by_cases ha : G 0 0 = 0
  · refine ⟨![1, 0], fun h => one_ne_zero (congrFun h 0), ?_⟩
    rw [H.linearFirst_eq_dotProduct]
    change dotProduct (fun i => c.bar (![1, 0] i)) (G.mulVec ![1, 0]) = 0
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, ha]
  · let t := (b - G 0 1) / G 0 0
    have ht : G 0 0 * t + G 0 1 = b := by
      dsimp [t]
      field_simp
      ring
    refine ⟨![t, 1], fun h => one_ne_zero (congrFun h 1), ?_⟩
    rw [H.linearFirst_eq_dotProduct]
    change dotProduct (fun i => c.bar (![t, 1] i)) (G.mulVec ![t, 1]) = 0
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, map_one, mul_one, one_mul, ht]
    rw [show c.bar t = (c.bar b - G 1 0) / G 0 0 by simp only [t, map_div₀, map_sub, hfix]]
    dsimp only [t]
    field_simp
    linear_combination hdet

end Langlands.GroupScheme.HermitianMatrix.Form
