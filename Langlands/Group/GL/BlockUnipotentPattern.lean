import Langlands.Group.GL.BlockUnipotent

/-!
# Block upper unipotent matrices from their entry pattern

An invertible matrix of size `a + b` that agrees with the identity matrix at every entry
outside the upper right `a × b` block is the block upper unipotent matrix
`blockUnipotent h X` of its upper right block `X`.
-/

noncomputable section

namespace Langlands.GeneralLinear

variable {R : Type*} [CommRing R] {a b n : ℕ}

/-- The standard consecutive numbering `Fin a ⊕ Fin b ≃ Fin n` used by `blockUnipotent`. -/
abbrev blockCut (h : a + b = n) : Fin a ⊕ Fin b ≃ Fin n :=
  finSumFinEquiv.trans (finCongr h)

@[simp]
theorem blockCut_inl_val (h : a + b = n) (i : Fin a) : (blockCut h (Sum.inl i)).val = i.val := by
  simp [blockCut]

@[simp]
theorem blockCut_inr_val (h : a + b = n) (j : Fin b) :
    (blockCut h (Sum.inr j)).val = a + j.val := by
  simp [blockCut]

theorem blockUnipotent_apply_blockCut (h : a + b = n) (X : Matrix (Fin a) (Fin b) R)
    (x y : Fin a ⊕ Fin b) :
    (blockUnipotent h X : Matrix (Fin n) (Fin n) R) (blockCut h x) (blockCut h y) =
      Matrix.fromBlocks 1 X 0 1 x y := by
  rw [blockUnipotent_val, Matrix.reindex_apply, Matrix.submatrix_apply]
  simp [blockCut]

/-- The upper right `a × b` block of a matrix of size `n = a + b`. -/
def upperRightBlock (h : a + b = n) (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin a) (Fin b) R :=
  Matrix.of fun i j => A (blockCut h (Sum.inl i)) (blockCut h (Sum.inr j))

/-- An invertible matrix equal to the identity outside the upper right block is the block
upper unipotent matrix of that block. -/
theorem eq_blockUnipotent_of_pattern (h : a + b = n) (g : GeneralLinear n R)
    (hg : ∀ i j : Fin n, (j.val < a ∨ a ≤ i.val) →
      (g : Matrix (Fin n) (Fin n) R) i j = if i = j then 1 else 0) :
    g = blockUnipotent h (upperRightBlock h (g : Matrix (Fin n) (Fin n) R)) := by
  apply Units.ext
  ext x y
  obtain ⟨x, rfl⟩ := (blockCut h).surjective x
  obtain ⟨y, rfl⟩ := (blockCut h).surjective y
  refine Eq.trans ?_ (blockUnipotent_apply_blockCut h _ x y).symm
  rcases x with i | i <;> rcases y with j | j
  · rw [hg _ _ (Or.inl (by simp))]
    simp [Matrix.one_apply]
  · simp [upperRightBlock]
  · rw [hg _ _ (Or.inr (by simp))]
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, ite_eq_right_iff]
    intro he
    have := congrArg Fin.val he
    simp at this
    omega
  · rw [hg _ _ (Or.inr (by simp))]
    simp [Matrix.one_apply]

end Langlands.GeneralLinear
