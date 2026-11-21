import Langlands.Group.GL.Blocks
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-! The block diagonal, strict upper block, and skew-adjoint decomposition. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.GeneralLinear.BlockShape

open scoped Matrix

variable {n : ℕ} (B : BlockShape n) {R : Type*} [AddCommGroup R] [StarAddMonoid R]

/-- The entries of a matrix whose row is in a strictly later block than its column. -/
def strictLowerBlockPart (X : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  fun a b => if B.coordinateBlock b < B.coordinateBlock a then X a b else 0

/-- The three matrix subspaces used to differentiate at a compact parameter. -/
theorem exists_blockDiagonal_strictUpper_skew (X : Matrix (Fin n) (Fin n) R) :
    ∃ (D : ∀ i, Matrix (Fin (B.size i)) (Fin (B.size i)) R)
      (U C : Matrix (Fin n) (Fin n) R),
      star C = -C ∧
      (∀ a b, B.coordinateBlock b ≤ B.coordinateBlock a → U a b = 0) ∧
      X = Matrix.reindex B.indexEquiv B.indexEquiv (Matrix.blockDiagonal' D) + U + C := by
  let D (i : Fin B.length) : Matrix (Fin (B.size i)) (Fin (B.size i)) R :=
    fun a b => X (B.index i a) (B.index i b)
  let D₀ := Matrix.reindex B.indexEquiv B.indexEquiv (Matrix.blockDiagonal' D)
  let L := B.strictLowerBlockPart X
  let C := L - star L
  let U := X - D₀ - C
  have hD (a b : Fin n) : D₀ a b = if B.coordinateBlock a = B.coordinateBlock b then X a b else 0 := by
    obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective a
    obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective b
    change Matrix.blockDiagonal' D (B.indexEquiv.symm (B.indexEquiv ⟨i, a⟩))
      (B.indexEquiv.symm (B.indexEquiv ⟨j, b⟩)) = _
    simp only [coordinateBlock, Equiv.symm_apply_apply]
    by_cases hij : i = j
    · subst j
      rw [Matrix.blockDiagonal'_apply_eq, ite_eq_left rfl]
      rfl
    · simp [Matrix.blockDiagonal'_apply_ne D a b hij, hij]
  refine ⟨D, U, C, ?_, ?_, ?_⟩
  · simp [C, star_sub, neg_sub]
  · intro a b h
    change X a b - D₀ a b - (L a b - star (L b a)) = 0
    rw [hD]
    rcases h.lt_or_eq with hlt | heq
    · simp [L, strictLowerBlockPart, hlt, (ne_of_lt hlt).symm, not_lt_of_ge h]
    · simp [L, strictLowerBlockPart, heq]
  · change X = D₀ + (X - D₀ - C) + C
    abel

end Langlands.GeneralLinear.BlockShape
