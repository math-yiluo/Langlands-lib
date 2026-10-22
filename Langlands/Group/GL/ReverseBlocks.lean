import Langlands.Group.GL.OppositeBlocks
import Langlands.Group.GL.Maps

namespace Langlands.GeneralLinear.BlockShape

universe u
variable {n : ℕ} (B : BlockShape n)

/-- Reverse the ordered list of positive block sizes, preserving total rank. -/
def reverse : BlockShape n where
  length := B.length
  size i := B.size i.rev
  positive i := B.positive i.rev
  sum_eq := (Equiv.sum_comp Fin.revPerm B.size).trans B.sum_eq

@[simp] theorem reverse_length : B.reverse.length = B.length := rfl
@[simp] theorem reverse_size (i : Fin B.length) : B.reverse.size i = B.size i.rev := rfl

/-- Reverse block labels while retaining each coordinate within its block. -/
def reverseIndexEquiv : B.reverse.Index ≃ B.Index :=
  Equiv.sigmaCongrLeft (β := fun i : Fin B.length => Fin (B.size i)) Fin.revPerm

/-- The permutation sending reversed-shape coordinates to original-shape coordinates. -/
def reversePermutation : Equiv.Perm (Fin n) :=
  B.reverse.indexEquiv.symm.trans (B.reverseIndexEquiv.trans B.indexEquiv)

@[simp] theorem reversePermutation_index (i : Fin B.length) (a : Fin (B.size i.rev)) :
    B.reversePermutation (B.reverse.index i a) = B.index i.rev a := by
  change B.indexEquiv (B.reverseIndexEquiv
    (B.reverse.indexEquiv.symm (B.reverse.indexEquiv ⟨i, a⟩))) = B.indexEquiv ⟨i.rev, a⟩
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem reversePermutation_symm_index (i : Fin B.length)
    (a : Fin (B.size i.rev)) :
    B.reversePermutation.symm (B.index i.rev a) = B.reverse.index i a := by
  apply B.reversePermutation.injective
  simp only [Equiv.apply_symm_apply, reversePermutation_index]

variable (R : Type u) [CommRing R]

/-- An actual matrix unit reversing the block order. -/
def reverseMatrix : Langlands.GeneralLinear n R :=
  permutation n R B.reversePermutation

/-- Conjugation transports entries between the corresponding block coordinates. -/
theorem reverseMatrix_conjugate_entry (g : Langlands.GeneralLinear n R)
    (i j : Fin B.length) (a : Fin (B.size i.rev)) (b : Fin (B.size j.rev)) :
    MulAut.conj (B.reverseMatrix R) g (B.index i.rev a) (B.index j.rev b) =
      g (B.reverse.index i a) (B.reverse.index j b) := by
  change (permutation n R B.reversePermutation * g *
    (permutation n R B.reversePermutation)⁻¹) _ _ = _
  rw [permutation_conjugate_entry]
  exact congrArg₂ g (B.reversePermutation_symm_index i a)
    (B.reversePermutation_symm_index j b)

/-- Upper reversed blocks become lower original blocks under the constructed matrix. -/
theorem reverseMatrix_conj_mem_oppositeParabolic_iff (g : Langlands.GeneralLinear n R) :
    MulAut.conj (B.reverseMatrix R) g ∈ B.oppositeParabolic R ↔
      g ∈ B.reverse.parabolic R := by
  rw [mem_oppositeParabolic_iff, mem_parabolic_iff]
  constructor
  · intro h i j a b hij
    rw [← B.reverseMatrix_conjugate_entry R g i j a b]
    exact h i.rev j.rev a b (Fin.rev_lt_rev.mpr hij)
  · intro h i j a b hij
    obtain ⟨i, rfl⟩ := Fin.rev_surjective i
    obtain ⟨j, rfl⟩ := Fin.rev_surjective j
    rw [reverseMatrix_conjugate_entry]
    exact h i j a b (Fin.rev_lt_rev.mp hij)

/-- Lower reversed blocks become upper original blocks under the same matrix. -/
theorem reverseMatrix_conj_mem_parabolic_iff (g : Langlands.GeneralLinear n R) :
    MulAut.conj (B.reverseMatrix R) g ∈ B.parabolic R ↔
      g ∈ B.reverse.oppositeParabolic R := by
  rw [mem_parabolic_iff, mem_oppositeParabolic_iff]
  constructor
  · intro h i j a b hij
    rw [← B.reverseMatrix_conjugate_entry R g i j a b]
    exact h i.rev j.rev a b (Fin.rev_lt_rev.mpr hij)
  · intro h i j a b hij
    obtain ⟨i, rfl⟩ := Fin.rev_surjective i
    obtain ⟨j, rfl⟩ := Fin.rev_surjective j
    rw [reverseMatrix_conjugate_entry]
    exact h i j a b (Fin.rev_lt_rev.mp hij)

private theorem reverseMatrix_conj_diagonal_iff (g : Langlands.GeneralLinear n R) :
    (∀ (i : Fin B.length) (a b : Fin (B.size i)),
      MulAut.conj (B.reverseMatrix R) g (B.index i a) (B.index i b) =
        if a = b then 1 else 0) ↔
    (∀ (i : Fin B.reverse.length) (a b : Fin (B.reverse.size i)),
      g (B.reverse.index i a) (B.reverse.index i b) = if a = b then 1 else 0) := by
  constructor
  · intro h i a b
    rw [← B.reverseMatrix_conjugate_entry R g i i a b]
    exact h i.rev a b
  · intro h i a b
    obtain ⟨i, rfl⟩ := Fin.rev_surjective i
    rw [reverseMatrix_conjugate_entry]
    exact h i a b

/-- The constructed conjugation identifies the two actual radical carriers. -/
theorem reverseMatrix_conj_mem_oppositeUnipotentSubgroup_iff
    (g : Langlands.GeneralLinear n R) :
    MulAut.conj (B.reverseMatrix R) g ∈ B.oppositeUnipotentSubgroup R ↔
      g ∈ B.reverse.unipotentSubgroup R := by
  rw [mem_oppositeUnipotentSubgroup_iff, mem_unipotentSubgroup_iff,
    reverseMatrix_conj_mem_oppositeParabolic_iff, reverseMatrix_conj_diagonal_iff]

/-- The same conjugation identifies the radicals in the other orientation. -/
theorem reverseMatrix_conj_mem_unipotentSubgroup_iff
    (g : Langlands.GeneralLinear n R) :
    MulAut.conj (B.reverseMatrix R) g ∈ B.unipotentSubgroup R ↔
      g ∈ B.reverse.oppositeUnipotentSubgroup R := by
  rw [mem_unipotentSubgroup_iff, mem_oppositeUnipotentSubgroup_iff,
    reverseMatrix_conj_mem_parabolic_iff, reverseMatrix_conj_diagonal_iff]

/-- The upper radical of the reversed shape maps onto the original opposite radical. -/
theorem reverse_unipotentSubgroup_map_conj :
    (B.reverse.unipotentSubgroup R).map (MulAut.conj (B.reverseMatrix R)).toMonoidHom =
      B.oppositeUnipotentSubgroup R := by
  ext g
  rw [Subgroup.mem_map_equiv]
  simpa only [MulEquiv.apply_symm_apply] using
    (B.reverseMatrix_conj_mem_oppositeUnipotentSubgroup_iff R
      ((MulAut.conj (B.reverseMatrix R)).symm g)).symm

/-- The opposite radical of the reversed shape maps onto the original upper radical. -/
theorem reverse_oppositeUnipotentSubgroup_map_conj :
    (B.reverse.oppositeUnipotentSubgroup R).map
      (MulAut.conj (B.reverseMatrix R)).toMonoidHom = B.unipotentSubgroup R := by
  ext g
  rw [Subgroup.mem_map_equiv]
  simpa only [MulEquiv.apply_symm_apply] using
    (B.reverseMatrix_conj_mem_unipotentSubgroup_iff R
      ((MulAut.conj (B.reverseMatrix R)).symm g)).symm

/-- Inverse transpose exchanges the original upper and lower parabolics. -/
theorem inverseTranspose_mem_oppositeParabolic_iff (g : Langlands.GeneralLinear n R) :
    inverseTranspose n R g ∈ B.oppositeParabolic R ↔ g ∈ B.parabolic R := by
  rw [← (B.parabolic R).inv_mem_iff, mem_oppositeParabolic_iff, mem_parabolic_iff]
  constructor
  · intro h i j a b hij
    exact h j i b a hij
  · intro h i j a b hij
    exact h j i b a hij

/-- Upper and lower standard parabolics are simultaneously the whole group. -/
theorem oppositeParabolic_eq_top_iff : B.oppositeParabolic R = ⊤ ↔ B.parabolic R = ⊤ := by
  rw [Subgroup.eq_top_iff', Subgroup.eq_top_iff']
  constructor
  · intro h g
    exact (B.inverseTranspose_mem_oppositeParabolic_iff R g).mp (h _)
  · intro h g
    obtain ⟨g, rfl⟩ := (inverseTranspose n R).surjective g
    exact (B.inverseTranspose_mem_oppositeParabolic_iff R g).mpr (h g)

/-- Reversing the block sizes preserves whether the parabolic is the whole group. -/
theorem reverse_parabolic_eq_top_iff : B.reverse.parabolic R = ⊤ ↔ B.parabolic R = ⊤ := by
  rw [← B.oppositeParabolic_eq_top_iff R, Subgroup.eq_top_iff', Subgroup.eq_top_iff']
  constructor
  · intro h g
    obtain ⟨g, rfl⟩ := (MulAut.conj (B.reverseMatrix R)).surjective g
    exact (B.reverseMatrix_conj_mem_oppositeParabolic_iff R g).mpr (h g)
  · intro h g
    exact (B.reverseMatrix_conj_mem_oppositeParabolic_iff R g).mp (h _)

/-- Properness is preserved, including the empty and one-block cases. -/
theorem reverse_parabolic_ne_top_iff :
    B.reverse.parabolic R ≠ ⊤ ↔ B.parabolic R ≠ ⊤ :=
  not_congr (B.reverse_parabolic_eq_top_iff R)

end Langlands.GeneralLinear.BlockShape
