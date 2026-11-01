import Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientData
import Langlands.Group.GL.ReverseBlocks

/-!
# The Section 4.7 lower block-unipotent quotient and its character

JPSS (1983), Section 4.7, equation (1), printed pages 412-413: the right side is an
integral over `H_(t_1,t_2) \ G_r`, where `H_(t_1,t_2)` is the unipotent group of matrices
`[[n_1, 0], [x, n_2]]` with `n_i ∈ N_(t_i)` and arbitrary lower-left block `x`, and the
integrand involves `W(w' g)` with `w' = w_r diag(w_(t_1), w_(t_2))`.

For two blocks of sizes `m 0 + 1` and `m 1 + 1` of total rank `t + 1`, this module
constructs the matrix `C = w'` as the inverse of the published block-reversing permutation
matrix, the subgroup `H⁻ = C⁻¹ N C`, its block description, the conjugation isomorphism
`H⁻ ≃* N`, the left quotient `H⁻ \ GL_(t+1)` with its identification
`[g] ↦ [C g]` with `N \ GL_(t+1)`, the pulled-back character with its explicit block formula,
and the determinant order and slices of the quotient. No measure, integral or
convergence statement is asserted.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient

open GeneralLinear TwoBlockJacquet TwoBlockDeformation QuotientIntegration Whittaker
  HarmonicAnalysis

universe uF uR

/-! ### The block rotation `w' = w_N diag(w_a, w_b)` -/

section Rotation

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The reversed block ranks `(m 1 + 1, m 0 + 1)` have the same total rank. -/
theorem reverse_sum (h : ∑ i, (m i + 1) = t + 1) : ∑ i : Fin 2, (m i.rev + 1) = t + 1 :=
  (Equiv.sum_comp Fin.revPerm (fun i => m i + 1)).trans h

/-- The published reversed shape is the successor shape of the reversed ranks. -/
theorem reverse_succBlockShape :
    (succBlockShape m h).reverse = succBlockShape (fun i => m i.rev) (reverse_sum h) :=
  rfl

/-- Every coordinate lies in exactly one block: it is coordinate `a` of some block `i`. -/
theorem exists_index_eq (k : Fin (t + 1)) :
    ∃ (i : Fin 2) (a : Fin (m i + 1)), (succBlockShape m h).index i a = k := by
  obtain ⟨⟨i, a⟩, rfl⟩ := (succBlockShape m h).indexEquiv.surjective k
  exact ⟨i, a, rfl⟩

/-- The inverse block-reversing permutation sends the first original block to the second
reversed block, keeping the coordinate. -/
theorem reversePermutation_symm_index_zero (a : Fin (m 0 + 1)) :
    (succBlockShape m h).reversePermutation.symm ((succBlockShape m h).index 0 a) =
      (succBlockShape (fun i => m i.rev) (reverse_sum h)).index 1 a := by
  have e : (succBlockShape m h).reversePermutation.symm
      ((succBlockShape m h).index (Fin.rev 1) a) =
      (succBlockShape (fun i => m i.rev) (reverse_sum h)).index 1 a :=
    (succBlockShape m h).reversePermutation_symm_index 1 a
  have e0 : (succBlockShape m h).index (Fin.rev 1) a = (succBlockShape m h).index 0 a := rfl
  rw [e0] at e
  exact e

/-- The inverse block-reversing permutation sends the second original block to the first
reversed block, keeping the coordinate. -/
theorem reversePermutation_symm_index_one (b : Fin (m 1 + 1)) :
    (succBlockShape m h).reversePermutation.symm ((succBlockShape m h).index 1 b) =
      (succBlockShape (fun i => m i.rev) (reverse_sum h)).index 0 b := by
  have e : (succBlockShape m h).reversePermutation.symm
      ((succBlockShape m h).index (Fin.rev 0) b) =
      (succBlockShape (fun i => m i.rev) (reverse_sum h)).index 0 b :=
    (succBlockShape m h).reversePermutation_symm_index 0 b
  have e0 : (succBlockShape m h).index (Fin.rev 0) b = (succBlockShape m h).index 1 b := rfl
  rw [e0] at e
  exact e

/-- The inverse block-reversing permutation sends coordinate `a` of the first block to
position `m 1 + 1 + a`, behind the whole second block. -/
theorem val_reversePermutation_symm_index_zero (a : Fin (m 0 + 1)) :
    ((succBlockShape m h).reversePermutation.symm ((succBlockShape m h).index 0 a) : ℕ) =
      m 1 + 1 + a := by
  rw [reversePermutation_symm_index_zero]
  exact val_index_one (reverse_sum h) a

/-- The inverse block-reversing permutation sends coordinate `b` of the second block to
position `b`, in front of the first block. -/
theorem val_reversePermutation_symm_index_one (b : Fin (m 1 + 1)) :
    ((succBlockShape m h).reversePermutation.symm ((succBlockShape m h).index 1 b) : ℕ) =
      b := by
  rw [reversePermutation_symm_index_one]
  exact val_index_zero (reverse_sum h) b

/-- Within each block, the inverse block-reversing permutation preserves the order of
coordinates. -/
theorem reversePermutation_symm_index_lt (i : Fin 2) {a b : Fin (m i + 1)} (hab : b < a) :
    (succBlockShape m h).reversePermutation.symm ((succBlockShape m h).index i b) <
      (succBlockShape m h).reversePermutation.symm ((succBlockShape m h).index i a) := by
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rw [Fin.lt_def] at hab ⊢
  rcases hi with rfl | rfl
  · rw [val_reversePermutation_symm_index_zero, val_reversePermutation_symm_index_zero]
    omega
  · rw [val_reversePermutation_symm_index_one, val_reversePermutation_symm_index_one]
    exact hab

/-- The inverse block-reversing permutation is the long Weyl reversal of the coordinate
reversed inside its own block. -/
theorem reversePermutation_symm_index_eq_rev (j : Fin 2) (y : Fin (m j + 1)) :
    (succBlockShape m h).reversePermutation.symm ((succBlockShape m h).index j y) =
      ((succBlockShape m h).index j y.rev).rev := by
  have hN := blockRanks_add h
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  apply Fin.ext
  rw [Fin.val_rev]
  rcases hj with rfl | rfl
  · rw [val_reversePermutation_symm_index_zero, val_index_zero, Fin.val_rev]
    have := y.isLt
    omega
  · rw [val_reversePermutation_symm_index_one, val_index_one, Fin.val_rev]
    have := y.isLt
    omega

variable (R : Type uR) [CommRing R]

/-- The block rotation `C` of JPSS (4.7): the inverse of the published block-reversing
permutation matrix. It moves the first block behind the second, keeping the order of
coordinates inside each block. -/
def blockRotation : GeneralLinear (t + 1) R :=
  ((succBlockShape m h).reverseMatrix R)⁻¹

/-- `C` is the permutation matrix of the inverse block-reversing permutation. -/
theorem blockRotation_eq_permutation :
    blockRotation h R = permutation (t + 1) R (succBlockShape m h).reversePermutation.symm :=
  permutation_inv (t + 1) R (succBlockShape m h).reversePermutation

/-- Inverse law: `C⁻¹` is the published block-reversing matrix. -/
@[simp]
theorem blockRotation_inv : (blockRotation h R)⁻¹ = (succBlockShape m h).reverseMatrix R :=
  inv_inv _

theorem blockRotation_mul_reverseMatrix :
    blockRotation h R * (succBlockShape m h).reverseMatrix R = 1 :=
  inv_mul_cancel _

theorem reverseMatrix_mul_blockRotation :
    (succBlockShape m h).reverseMatrix R * blockRotation h R = 1 :=
  mul_inv_cancel _

/-- Entries of `C`: column `l` is the unit vector at the position `σ⁻¹ l`. -/
theorem blockRotation_apply (k l : Fin (t + 1)) :
    blockRotation h R k l =
      if (succBlockShape m h).reversePermutation.symm l = k then 1 else 0 := by
  rw [blockRotation_eq_permutation]
  exact permutation_entry (t + 1) R _ k l

/-- Entries of `C⁻¹`: column `l` is the unit vector at the position `σ l`. -/
theorem blockRotation_inv_apply (k l : Fin (t + 1)) :
    (blockRotation h R)⁻¹ k l =
      if (succBlockShape m h).reversePermutation l = k then 1 else 0 := by
  rw [blockRotation_inv]
  exact permutation_entry (t + 1) R _ k l

/-- Coordinate law: column `a` of the first block of `C` is the unit vector at position
`m 1 + 1 + a`. -/
theorem blockRotation_apply_index_zero (k : Fin (t + 1)) (a : Fin (m 0 + 1)) :
    blockRotation h R k ((succBlockShape m h).index 0 a) =
      if (k : ℕ) = m 1 + 1 + a then 1 else 0 := by
  rw [blockRotation_apply]
  have hv := val_reversePermutation_symm_index_zero h a
  by_cases hk : (k : ℕ) = m 1 + 1 + a
  · rw [ite_eq_left (Fin.ext (hv.trans hk.symm)), ite_eq_left hk]
  · rw [ite_eq_right (fun e => hk ((congrArg Fin.val e).symm.trans hv)), ite_eq_right hk]

/-- Coordinate law: column `b` of the second block of `C` is the unit vector at
position `b`. -/
theorem blockRotation_apply_index_one (k : Fin (t + 1)) (b : Fin (m 1 + 1)) :
    blockRotation h R k ((succBlockShape m h).index 1 b) =
      if (k : ℕ) = b then 1 else 0 := by
  rw [blockRotation_apply]
  have hv := val_reversePermutation_symm_index_one h b
  by_cases hk : (k : ℕ) = b
  · rw [ite_eq_left (Fin.ext (hv.trans hk.symm)), ite_eq_left hk]
  · rw [ite_eq_right (fun e => hk ((congrArg Fin.val e).symm.trans hv)), ite_eq_right hk]

/-- Coordinate law for the inverse: row `a` of the first block of `C⁻¹` is the unit row
at position `m 1 + 1 + a`. -/
theorem blockRotation_inv_apply_index_zero (a : Fin (m 0 + 1)) (l : Fin (t + 1)) :
    (blockRotation h R)⁻¹ ((succBlockShape m h).index 0 a) l =
      if (l : ℕ) = m 1 + 1 + a then 1 else 0 := by
  rw [blockRotation_inv_apply]
  have hv := val_reversePermutation_symm_index_zero h a
  by_cases hl : (l : ℕ) = m 1 + 1 + a
  · have e : l = (succBlockShape m h).reversePermutation.symm ((succBlockShape m h).index 0 a) :=
      Fin.ext (hl.trans hv.symm)
    rw [ite_eq_left (by rw [e, Equiv.apply_symm_apply]), ite_eq_left hl]
  · rw [ite_eq_right, ite_eq_right hl]
    intro e
    apply hl
    rw [← hv, ← e, Equiv.symm_apply_apply]

/-- Coordinate law for the inverse: row `b` of the second block of `C⁻¹` is the unit row
at position `b`. -/
theorem blockRotation_inv_apply_index_one (b : Fin (m 1 + 1)) (l : Fin (t + 1)) :
    (blockRotation h R)⁻¹ ((succBlockShape m h).index 1 b) l =
      if (l : ℕ) = b then 1 else 0 := by
  rw [blockRotation_inv_apply]
  have hv := val_reversePermutation_symm_index_one h b
  by_cases hl : (l : ℕ) = b
  · have e : l = (succBlockShape m h).reversePermutation.symm ((succBlockShape m h).index 1 b) :=
      Fin.ext (hl.trans hv.symm)
    rw [ite_eq_left (by rw [e, Equiv.apply_symm_apply]), ite_eq_left hl]
  · rw [ite_eq_right, ite_eq_right hl]
    intro e
    apply hl
    rw [← hv, ← e, Equiv.symm_apply_apply]

/-- Left multiplication by `C` permutes rows: row `k` of `C g` is row `σ k` of `g`. -/
theorem blockRotation_mul_apply (g : GeneralLinear (t + 1) R) (k l : Fin (t + 1)) :
    (blockRotation h R * g) k l = g ((succBlockShape m h).reversePermutation k) l := by
  rw [blockRotation_eq_permutation]
  exact permutation_mul_entry (t + 1) R _ g k l

/-- Conjugation by `C` permutes both coordinates by `σ`. -/
theorem blockRotation_conj_apply (g : GeneralLinear (t + 1) R) (k l : Fin (t + 1)) :
    (blockRotation h R * g * (blockRotation h R)⁻¹) k l =
      g ((succBlockShape m h).reversePermutation k) ((succBlockShape m h).reversePermutation l) := by
  rw [blockRotation_eq_permutation]
  exact permutation_conjugate_entry (t + 1) R _ g k l

theorem blockRotation_conj_apply_symm (g : GeneralLinear (t + 1) R) (k l : Fin (t + 1)) :
    (blockRotation h R * g * (blockRotation h R)⁻¹)
        ((succBlockShape m h).reversePermutation.symm k)
        ((succBlockShape m h).reversePermutation.symm l) = g k l := by
  rw [blockRotation_conj_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Inverse conjugation permutes both coordinates by `σ⁻¹`. -/
theorem blockRotation_inv_conj_apply (n : GeneralLinear (t + 1) R) (k l : Fin (t + 1)) :
    ((blockRotation h R)⁻¹ * n * blockRotation h R) k l =
      n ((succBlockShape m h).reversePermutation.symm k)
        ((succBlockShape m h).reversePermutation.symm l) := by
  rw [blockRotation_inv]
  exact permutation_conjugate_entry (t + 1) R _ n k l

/-- In reversed block coordinates, conjugation by `C` reads the entries of the original
blocks: the reversed block `i` is the original block `i.rev`. -/
theorem blockRotation_conj_apply_reverse_index (g : GeneralLinear (t + 1) R) (i j : Fin 2)
    (x : Fin (m i.rev + 1)) (y : Fin (m j.rev + 1)) :
    (blockRotation h R * g * (blockRotation h R)⁻¹)
        ((succBlockShape (fun i => m i.rev) (reverse_sum h)).index i x)
        ((succBlockShape (fun i => m i.rev) (reverse_sum h)).index j y) =
      g ((succBlockShape m h).index i.rev x) ((succBlockShape m h).index j.rev y) := by
  rw [blockRotation_conj_apply]
  exact congrArg₂ (fun k l => g k l) ((succBlockShape m h).reversePermutation_index i x)
    ((succBlockShape m h).reversePermutation_index j y)

/-- Columns of `diag(w_a, w_b)`: column `y` of block `j` is the unit vector at coordinate
`y.rev` of the same block. -/
theorem leviEmbedding_weylLong_apply_index (k : Fin (t + 1)) (j : Fin 2) (y : Fin (m j + 1)) :
    (succBlockShape m h).leviEmbedding R (fun i => weylLong (m i + 1) R) k
        ((succBlockShape m h).index j y) =
      if k = (succBlockShape m h).index j y.rev then 1 else 0 := by
  obtain ⟨⟨i, x⟩, rfl⟩ := (succBlockShape m h).indexEquiv.surjective k
  change (succBlockShape m h).leviEmbedding R (fun i => weylLong (m i + 1) R)
      ((succBlockShape m h).index i x) ((succBlockShape m h).index j y) =
    if (succBlockShape m h).index i x = (succBlockShape m h).index j y.rev then 1 else 0
  by_cases hij : i = j
  · subst hij
    rw [BlockShape.leviEmbedding_apply_same, weylLong_entry]
    by_cases hx : y.rev = x
    · rw [ite_eq_left hx, ite_eq_left (by rw [hx])]
    · rw [ite_eq_right hx, ite_eq_right]
      intro e
      exact hx (((succBlockShape m h).index i).injective e).symm
  · rw [BlockShape.leviEmbedding_apply_ne _ _ _ _ _ hij, ite_eq_right]
    intro e
    exact hij (congrArg Sigma.fst ((succBlockShape m h).indexEquiv.injective e))

/-- JPSS (4.7), printed page 413: `C = w' = w_N diag(w_a, w_b)`. -/
theorem blockRotation_eq_weylLong_mul_leviEmbedding :
    blockRotation h R =
      weylLong (t + 1) R *
        (succBlockShape m h).leviEmbedding R (fun i => weylLong (m i + 1) R) := by
  apply Units.ext
  ext k l
  obtain ⟨⟨j, y⟩, rfl⟩ := (succBlockShape m h).indexEquiv.surjective l
  change blockRotation h R k ((succBlockShape m h).index j y) =
    (weylLong (t + 1) R *
      (succBlockShape m h).leviEmbedding R (fun i => weylLong (m i + 1) R)) k
      ((succBlockShape m h).index j y)
  rw [weylLong_mul_entry, leviEmbedding_weylLong_apply_index, blockRotation_apply,
    reversePermutation_symm_index_eq_rev]
  have hiff : ((succBlockShape m h).index j y.rev).rev = k ↔
      k.rev = (succBlockShape m h).index j y.rev := by
    constructor
    · rintro rfl
      exact Fin.rev_rev _
    · rintro e
      rw [← e, Fin.rev_rev]
  by_cases hk : k.rev = (succBlockShape m h).index j y.rev
  · rw [ite_eq_left (hiff.mpr hk), ite_eq_left hk]
  · rw [ite_eq_right (mt hiff.mp hk), ite_eq_right hk]

end Rotation

/-! ### The subgroup `H⁻ = C⁻¹ N C` -/

section Subgroup

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (R : Type uR) [CommRing R]

/-- The subgroup `H_(t_1,t_2)` of JPSS (4.7), printed page 413: the invertible matrices `g`
with `C g C⁻¹` upper unipotent. -/
def lowerBlockUnipotent : Subgroup (GeneralLinear (t + 1) R) :=
  (upperUnipotent (t + 1) R).comap (MulAut.conj (blockRotation h R)).toMonoidHom

theorem mem_lowerBlockUnipotent_iff_conj (g : GeneralLinear (t + 1) R) :
    g ∈ lowerBlockUnipotent h R ↔
      blockRotation h R * g * (blockRotation h R)⁻¹ ∈ upperUnipotent (t + 1) R :=
  Iff.rfl

/-- A pair of block positions that `σ⁻¹` puts strictly below the diagonal lies in the
upper-right block or strictly below the diagonal of a diagonal block. -/
theorem entry_eq_zero_of_reversePermutation_symm_lt {g : GeneralLinear (t + 1) R}
    (h01 : ∀ (a : Fin (m 0 + 1)) (b : Fin (m 1 + 1)),
      g ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b) = 0)
    (hlow : ∀ (i : Fin 2) (a b : Fin (m i + 1)), b < a →
      g ((succBlockShape m h).index i a) ((succBlockShape m h).index i b) = 0)
    (i j : Fin (succBlockShape m h).length) (a : Fin (m i + 1)) (b : Fin (m j + 1))
    (hlk : ((succBlockShape m h).reversePermutation.symm ((succBlockShape m h).index j b) : ℕ) <
      (succBlockShape m h).reversePermutation.symm ((succBlockShape m h).index i a)) :
    g ((succBlockShape m h).index i a) ((succBlockShape m h).index j b) = 0 := by
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · rw [val_reversePermutation_symm_index_zero,
      val_reversePermutation_symm_index_zero] at hlk
    exact hlow 0 a b (Fin.lt_def.mpr (by omega))
  · exact h01 a b
  · rw [val_reversePermutation_symm_index_zero,
      val_reversePermutation_symm_index_one] at hlk
    exact absurd hlk (by have := a.isLt; omega)
  · rw [val_reversePermutation_symm_index_one,
      val_reversePermutation_symm_index_one] at hlk
    exact hlow 1 a b (Fin.lt_def.mpr hlk)

/-- The block conditions of `H⁻` hold for every element of `H⁻`. -/
theorem blocks_of_mem_lowerBlockUnipotent {g : GeneralLinear (t + 1) R}
    (hn : g ∈ lowerBlockUnipotent h R) :
      (∀ (a : Fin (m 0 + 1)) (b : Fin (m 1 + 1)),
        g ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b) = 0) ∧
      (∀ (i : Fin 2) (a b : Fin (m i + 1)), b < a →
        g ((succBlockShape m h).index i a) ((succBlockShape m h).index i b) = 0) ∧
      (∀ (i : Fin 2) (a : Fin (m i + 1)),
        g ((succBlockShape m h).index i a) ((succBlockShape m h).index i a) = 1) := by
  rw [mem_lowerBlockUnipotent_iff_conj] at hn
  let n : upperUnipotent (t + 1) R := ⟨_, hn⟩
  have hg : ∀ k l, g k l = n.val ((succBlockShape m h).reversePermutation.symm k)
      ((succBlockShape m h).reversePermutation.symm l) :=
    fun k l => (blockRotation_conj_apply_symm h R g k l).symm
  refine ⟨fun a b => ?_, fun i a b hab => ?_, fun i a => ?_⟩
  · rw [hg]
    apply UpperUnipotent.entry_eq_zero
    rw [Fin.lt_def, val_reversePermutation_symm_index_zero,
      val_reversePermutation_symm_index_one]
    omega
  · rw [hg]
    exact UpperUnipotent.entry_eq_zero n (reversePermutation_symm_index_lt h i hab)
  · rw [hg]
    exact UpperUnipotent.entry_diag n _

/-- The block conditions of `H⁻` characterize its elements. -/
theorem mem_lowerBlockUnipotent_of_blocks {g : GeneralLinear (t + 1) R}
    (h01 : ∀ (a : Fin (m 0 + 1)) (b : Fin (m 1 + 1)),
      g ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b) = 0)
    (hlow : ∀ (i : Fin 2) (a b : Fin (m i + 1)), b < a →
      g ((succBlockShape m h).index i a) ((succBlockShape m h).index i b) = 0)
    (hdiag : ∀ (i : Fin 2) (a : Fin (m i + 1)),
      g ((succBlockShape m h).index i a) ((succBlockShape m h).index i a) = 1) :
    g ∈ lowerBlockUnipotent h R := by
  rw [mem_lowerBlockUnipotent_iff_conj]
  refine ⟨fun k l hlk => ?_, fun k => ?_⟩
  · obtain ⟨i, a, hk⟩ := exists_index_eq h ((succBlockShape m h).reversePermutation k)
    obtain ⟨j, b, hl⟩ := exists_index_eq h ((succBlockShape m h).reversePermutation l)
    have hk' : k = (succBlockShape m h).reversePermutation.symm ((succBlockShape m h).index i a) :=
      by rw [hk, Equiv.symm_apply_apply]
    have hl' : l = (succBlockShape m h).reversePermutation.symm ((succBlockShape m h).index j b) :=
      by rw [hl, Equiv.symm_apply_apply]
    clear hk hl
    subst hk' hl'
    exact (blockRotation_conj_apply_symm h R g _ _).trans
      (entry_eq_zero_of_reversePermutation_symm_lt h R h01 hlow i j a b (Fin.lt_def.mp hlk))
  · obtain ⟨i, a, hk⟩ := exists_index_eq h ((succBlockShape m h).reversePermutation k)
    have hk' : k = (succBlockShape m h).reversePermutation.symm ((succBlockShape m h).index i a) :=
      by rw [hk, Equiv.symm_apply_apply]
    clear hk
    subst hk'
    exact (blockRotation_conj_apply_symm h R g _ _).trans (hdiag i a)

/-- Intrinsic block criterion: `g ∈ H⁻` exactly when its upper-right `a × b` block vanishes
and both diagonal blocks are upper unipotent. The lower-left block is not constrained. -/
theorem mem_lowerBlockUnipotent_iff (g : GeneralLinear (t + 1) R) :
    g ∈ lowerBlockUnipotent h R ↔
      (∀ (a : Fin (m 0 + 1)) (b : Fin (m 1 + 1)),
        g ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b) = 0) ∧
      (∀ (i : Fin 2) (a b : Fin (m i + 1)), b < a →
        g ((succBlockShape m h).index i a) ((succBlockShape m h).index i b) = 0) ∧
      (∀ (i : Fin 2) (a : Fin (m i + 1)),
        g ((succBlockShape m h).index i a) ((succBlockShape m h).index i a) = 1) :=
  ⟨blocks_of_mem_lowerBlockUnipotent h R, fun ⟨h01, hlow, hdiag⟩ =>
    mem_lowerBlockUnipotent_of_blocks h R h01 hlow hdiag⟩

/-- The upper-right block of an element of `H⁻` vanishes. -/
theorem index_zero_one_eq_zero {g : GeneralLinear (t + 1) R} (hg : g ∈ lowerBlockUnipotent h R)
    (a : Fin (m 0 + 1)) (b : Fin (m 1 + 1)) :
    g ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b) = 0 :=
  ((mem_lowerBlockUnipotent_iff h R g).mp hg).1 a b

/-- `H⁻` lies in the published lower block parabolic of `succBlockShape m h`. -/
theorem lowerBlockUnipotent_le_oppositeParabolic :
    lowerBlockUnipotent h R ≤ (succBlockShape m h).oppositeParabolic R := by
  intro g hg
  rw [BlockShape.mem_oppositeParabolic_iff]
  intro i j a b hij
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact absurd hij (lt_irrefl _)
  · exact index_zero_one_eq_zero h R hg a b
  · exact absurd hij (Fin.not_lt_zero _)
  · exact absurd hij (lt_irrefl _)

/-- The diagonal block `i` of `g ∈ H⁻`, read by the published opposite Levi projection, is
upper unipotent. -/
theorem oppositeLeviProjection_mem_upperUnipotent (g : lowerBlockUnipotent h R) (i : Fin 2) :
    (succBlockShape m h).oppositeLeviProjection R
        (Subgroup.inclusion (lowerBlockUnipotent_le_oppositeParabolic h R) g) i ∈
      upperUnipotent (m i + 1) R := by
  obtain ⟨-, hlow, hdiag⟩ := (mem_lowerBlockUnipotent_iff h R g.val).mp g.property
  exact ⟨fun a b hab => hlow i a b hab, fun a => hdiag i a⟩

/-- The diagonal blocks `(n_a, n_b)` of `g ∈ H⁻`, as an element of `N_a × N_b`. -/
def diagonalBlocks : lowerBlockUnipotent h R →* TwoBlockUnipotentQuotient.BlockUnipotents m R where
  toFun g i := ⟨(succBlockShape m h).oppositeLeviProjection R
      (Subgroup.inclusion (lowerBlockUnipotent_le_oppositeParabolic h R) g) i,
    oppositeLeviProjection_mem_upperUnipotent h R g i⟩
  map_one' := by
    funext i
    exact Subtype.ext (congrFun (map_one ((succBlockShape m h).oppositeLeviProjection R)) i)
  map_mul' g g' := by
    funext i
    exact Subtype.ext
      (congrFun (map_mul ((succBlockShape m h).oppositeLeviProjection R)
        (Subgroup.inclusion (lowerBlockUnipotent_le_oppositeParabolic h R) g)
        (Subgroup.inclusion (lowerBlockUnipotent_le_oppositeParabolic h R) g')) i)

/-- The entries of the diagonal block `i` of `g ∈ H⁻` are those of `g` in block `i`. -/
@[simp]
theorem diagonalBlocks_apply (g : lowerBlockUnipotent h R) (i : Fin 2) (a b : Fin (m i + 1)) :
    (diagonalBlocks h R g i).val a b =
      g.val ((succBlockShape m h).index i a) ((succBlockShape m h).index i b) :=
  rfl

/-- The displayed form `[[n_a, 0], [X, n_b]]` of JPSS (4.7): `g ∈ H⁻` exactly when its
upper-right block vanishes and its diagonal blocks are those of some `(n_a, n_b) ∈ N_a × N_b`. -/
theorem mem_lowerBlockUnipotent_iff_blocks (g : GeneralLinear (t + 1) R) :
    g ∈ lowerBlockUnipotent h R ↔
      (∀ (a : Fin (m 0 + 1)) (b : Fin (m 1 + 1)),
        g ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b) = 0) ∧
      ∃ n : TwoBlockUnipotentQuotient.BlockUnipotents m R, ∀ (i : Fin 2) (a b : Fin (m i + 1)),
        g ((succBlockShape m h).index i a) ((succBlockShape m h).index i b) = (n i).val a b := by
  constructor
  · intro hg
    exact ⟨index_zero_one_eq_zero h R hg, diagonalBlocks h R ⟨g, hg⟩, fun i a b => rfl⟩
  · rintro ⟨h01, n, hn⟩
    refine (mem_lowerBlockUnipotent_iff h R g).mpr ⟨h01, fun i a b hab => ?_, fun i a => ?_⟩
    · rw [hn]
      exact UpperUnipotent.entry_eq_zero (n i) hab
    · rw [hn]
      exact UpperUnipotent.entry_diag (n i) a

/-- The lower radical matrix `[[1, 0], [X, 1]]`, for an arbitrary `b × a` matrix `X`: the
conjugate `C⁻¹ u'(X) C` of the upper radical matrix `u'(X)` of the reversed block shape. -/
def lowerRadical (X : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R) : GeneralLinear (t + 1) R :=
  (blockRotation h R)⁻¹ * upperRadical (reverse_sum h) R X * blockRotation h R

/-- The lower-left block of the lower radical matrix is `X`. -/
@[simp]
theorem lowerRadical_index_one_zero (X : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R)
    (b : Fin (m 1 + 1)) (a : Fin (m 0 + 1)) :
    lowerRadical h R X ((succBlockShape m h).index 1 b) ((succBlockShape m h).index 0 a) =
      X b a := by
  rw [lowerRadical, blockRotation_inv_conj_apply, reversePermutation_symm_index_one,
    reversePermutation_symm_index_zero]
  exact upperRadical_index_zero_one (reverse_sum h) R X b a

@[simp]
theorem lowerRadical_index_zero_one (X : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R)
    (a : Fin (m 0 + 1)) (b : Fin (m 1 + 1)) :
    lowerRadical h R X ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b) = 0 := by
  rw [lowerRadical, blockRotation_inv_conj_apply, reversePermutation_symm_index_zero,
    reversePermutation_symm_index_one]
  exact upperRadical_index_one_zero (reverse_sum h) R X a b

@[simp]
theorem lowerRadical_index_zero_zero (X : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R)
    (a a' : Fin (m 0 + 1)) :
    lowerRadical h R X ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 0 a') =
      if a = a' then 1 else 0 := by
  rw [lowerRadical, blockRotation_inv_conj_apply, reversePermutation_symm_index_zero,
    reversePermutation_symm_index_zero]
  exact upperRadical_index_one_one (reverse_sum h) R X a a'

@[simp]
theorem lowerRadical_index_one_one (X : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R)
    (b b' : Fin (m 1 + 1)) :
    lowerRadical h R X ((succBlockShape m h).index 1 b) ((succBlockShape m h).index 1 b') =
      if b = b' then 1 else 0 := by
  rw [lowerRadical, blockRotation_inv_conj_apply, reversePermutation_symm_index_one,
    reversePermutation_symm_index_one]
  exact upperRadical_index_zero_zero (reverse_sum h) R X b b'

/-- The lower-left block of `H⁻` is arbitrary: every lower radical matrix lies in `H⁻`. -/
theorem lowerRadical_mem (X : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R) :
    lowerRadical h R X ∈ lowerBlockUnipotent h R := by
  rw [mem_lowerBlockUnipotent_iff_conj]
  have e : blockRotation h R * lowerRadical h R X * (blockRotation h R)⁻¹ =
      upperRadical (reverse_sum h) R X := by
    rw [lowerRadical]
    group
  rw [e]
  exact TwoBlockUnipotentQuotient.upperRadical_mem_upperUnipotent (reverse_sum h) R X

/-- The multiplicative equivalence `H⁻ ≃* N_(t+1)`, `g ↦ C g C⁻¹`. -/
def conjugationEquiv : lowerBlockUnipotent h R ≃* upperUnipotent (t + 1) R where
  toFun g := ⟨blockRotation h R * g.val * (blockRotation h R)⁻¹, g.property⟩
  invFun n := ⟨(blockRotation h R)⁻¹ * n.val * blockRotation h R, by
    rw [mem_lowerBlockUnipotent_iff_conj]
    have e : blockRotation h R * ((blockRotation h R)⁻¹ * n.val * blockRotation h R) *
        (blockRotation h R)⁻¹ = n.val := by group
    rw [e]
    exact n.property⟩
  left_inv g := Subtype.ext (show (blockRotation h R)⁻¹ *
      (blockRotation h R * g.val * (blockRotation h R)⁻¹) * blockRotation h R = g.val by group)
  right_inv n := Subtype.ext (show blockRotation h R *
      ((blockRotation h R)⁻¹ * n.val * blockRotation h R) * (blockRotation h R)⁻¹ = n.val by
    group)
  map_mul' g g' := Subtype.ext (show blockRotation h R * (g.val * g'.val) *
      (blockRotation h R)⁻¹ = blockRotation h R * g.val * (blockRotation h R)⁻¹ *
        (blockRotation h R * g'.val * (blockRotation h R)⁻¹) by group)

/-- Representative law: `conjugationEquiv g = C g C⁻¹`. -/
@[simp]
theorem conjugationEquiv_apply_val (g : lowerBlockUnipotent h R) :
    (conjugationEquiv h R g).val = blockRotation h R * g.val * (blockRotation h R)⁻¹ :=
  rfl

/-- Representative law: `conjugationEquiv⁻¹ n = C⁻¹ n C`. -/
@[simp]
theorem conjugationEquiv_symm_apply_val (n : upperUnipotent (t + 1) R) :
    ((conjugationEquiv h R).symm n).val = (blockRotation h R)⁻¹ * n.val * blockRotation h R :=
  rfl

/-- Every element of `H⁻` has determinant one. -/
theorem determinant_eq_one_of_mem_lowerBlockUnipotent {g : GeneralLinear (t + 1) R}
    (hg : g ∈ lowerBlockUnipotent h R) : GeneralLinear.determinant g = 1 := by
  have h1 : GeneralLinear.determinant (blockRotation h R * g * (blockRotation h R)⁻¹) = 1 :=
    TwoBlockUnipotentQuotient.determinant_eq_one_of_mem_upperUnipotent R
      ((mem_lowerBlockUnipotent_iff_conj h R g).mp hg)
  rwa [map_mul, map_mul, map_inv, mul_comm (GeneralLinear.determinant (blockRotation h R)),
    mul_inv_cancel_right] at h1

end Subgroup

/-! ### Topology of the subgroup -/

section Topology

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (R : Type uR) [CommRing R]
variable [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_conjugationEquiv : Continuous (conjugationEquiv h R) :=
  ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

theorem continuous_conjugationEquiv_symm : Continuous (conjugationEquiv h R).symm :=
  ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

/-- The conjugation `H⁻ ≃* N_(t+1)` as a continuous multiplicative equivalence. -/
def conjugationHomeomorph : lowerBlockUnipotent h R ≃ₜ* upperUnipotent (t + 1) R where
  toMulEquiv := conjugationEquiv h R
  continuous_toFun := continuous_conjugationEquiv h R
  continuous_invFun := continuous_conjugationEquiv_symm h R

@[simp]
theorem conjugationHomeomorph_toMulEquiv :
    (conjugationHomeomorph h R).toMulEquiv = conjugationEquiv h R :=
  rfl

/-- `H⁻` is closed in a Hausdorff topological ring: it is the preimage of the closed group
`N_(t+1)` under the continuous conjugation by `C`. -/
theorem isClosed_lowerBlockUnipotent [T2Space R] :
    IsClosed (lowerBlockUnipotent h R : Set (GeneralLinear (t + 1) R)) :=
  (UpperUnipotent.isClosed (R := R) (n := t + 1)).preimage
    ((continuous_const.mul continuous_id).mul continuous_const)

end Topology

section Canonical

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- For the canonical p-adic topology, `H⁻ ≃ₜ* N_(t+1)`. -/
def canonicalConjugationHomeomorph :
    letI := F.canonicalTopologicalData.topology
    lowerBlockUnipotent h F.Carrier ≃ₜ* upperUnipotent (t + 1) F.Carrier :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
  conjugationHomeomorph h F.Carrier

@[simp]
theorem canonicalConjugationHomeomorph_toMulEquiv :
    letI := F.canonicalTopologicalData.topology
    (canonicalConjugationHomeomorph F h).toMulEquiv = conjugationEquiv h F.Carrier :=
  rfl

/-- Continuity of `g ↦ C g C⁻¹` on `H⁻` for the canonical p-adic topology. -/
theorem continuous_conjugationEquiv_canonical :
    letI := F.canonicalTopologicalData.topology
    Continuous (conjugationEquiv h F.Carrier) :=
  letI := F.canonicalTopologicalData.topology
  (canonicalConjugationHomeomorph F h).continuous

/-- Continuity of `n ↦ C⁻¹ n C` on `N_(t+1)` for the canonical p-adic topology. -/
theorem continuous_conjugationEquiv_symm_canonical :
    letI := F.canonicalTopologicalData.topology
    Continuous (conjugationEquiv h F.Carrier).symm :=
  letI := F.canonicalTopologicalData.topology
  (canonicalConjugationHomeomorph F h).symm.continuous

/-- `H⁻` is closed in `GL_(t+1)(F)` for the canonical p-adic topology. -/
theorem isClosed_lowerBlockUnipotent_canonical :
    letI := F.canonicalTopologicalData.topology
    IsClosed (lowerBlockUnipotent h F.Carrier : Set (GeneralLinear (t + 1) F.Carrier)) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := F.canonicalTopologicalData.fieldT2
  exact isClosed_lowerBlockUnipotent h F.Carrier

end Canonical

/-! ### The quotient `H⁻ \ GL_(t+1)` and left multiplication by `C` -/

section Quotient

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (R : Type uR) [CommRing R]

/-- The actual left quotient `H⁻ \ GL_(t+1)` of JPSS (4.7), equation (1). -/
abbrev LowerQuotient := LeftQuotient (lowerBlockUnipotent h R)

/-- Left multiplication by `C` carries the coset relation of `H⁻` to that of `N_(t+1)`. -/
theorem rightRel_iff_blockRotation_mul (g k : GeneralLinear (t + 1) R) :
    QuotientGroup.rightRel (lowerBlockUnipotent h R) g k ↔
      QuotientGroup.rightRel (upperUnipotent (t + 1) R) (blockRotation h R * g)
        (blockRotation h R * k) := by
  rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply,
    mem_lowerBlockUnipotent_iff_conj]
  simp only [mul_inv_rev, mul_assoc]

/-- The identification `H⁻ \ GL_(t+1) ≃ N_(t+1) \ GL_(t+1)`, `[g] ↦ [C g]`. -/
def lowerToStandard : LowerQuotient h R ≃ LeftQuotient (upperUnipotent (t + 1) R) :=
  Quotient.congr (Equiv.mulLeft (blockRotation h R)) (rightRel_iff_blockRotation_mul h R)

/-- Representative law: `lowerToStandard [g] = [C g]`. -/
@[simp]
theorem lowerToStandard_mk (g : GeneralLinear (t + 1) R) :
    lowerToStandard h R (Quotient.mk _ g) = Quotient.mk _ (blockRotation h R * g) :=
  rfl

/-- Representative law: `lowerToStandard⁻¹ [g] = [C⁻¹ g]`. -/
@[simp]
theorem lowerToStandard_symm_mk (g : GeneralLinear (t + 1) R) :
    (lowerToStandard h R).symm (Quotient.mk _ g) =
      Quotient.mk _ ((blockRotation h R)⁻¹ * g) := by
  rw [Equiv.symm_apply_eq, lowerToStandard_mk, mul_inv_cancel_left]

/-- Left multiplication by `u ∈ H⁻` does not change `[C g]` in `N_(t+1) \ GL_(t+1)`. -/
theorem mk_blockRotation_mul_of_mem {u : GeneralLinear (t + 1) R}
    (hu : u ∈ lowerBlockUnipotent h R) (g : GeneralLinear (t + 1) R) :
    (Quotient.mk _ (blockRotation h R * (u * g)) : LeftQuotient (upperUnipotent (t + 1) R)) =
      Quotient.mk _ (blockRotation h R * g) := by
  have e : blockRotation h R * (u * g) =
      (blockRotation h R * u * (blockRotation h R)⁻¹) * (blockRotation h R * g) := by group
  rw [e]
  exact TwoBlockUnipotentQuotient.mk_mul_of_mem (upperUnipotent (t + 1) R)
    ((mem_lowerBlockUnipotent_iff_conj h R u).mp hu) _

/-- Descent: `lowerToStandard` is the descent of `g ↦ [C g]` along `GL_(t+1) → H⁻ \ GL_(t+1)`. -/
theorem lowerToStandard_eq_descend :
    ⇑(lowerToStandard h R) =
      descend (lowerBlockUnipotent h R)
        (fun g => (Quotient.mk _ (blockRotation h R * g) :
          LeftQuotient (upperUnipotent (t + 1) R)))
        (fun u g => mk_blockRotation_mul_of_mem h R u.property g) := by
  funext q
  induction q using Quotient.inductionOn with
  | h g => rfl

@[simp]
theorem lowerToStandard_symm_apply_apply (q : LowerQuotient h R) :
    (lowerToStandard h R).symm (lowerToStandard h R q) = q :=
  (lowerToStandard h R).symm_apply_apply q

@[simp]
theorem lowerToStandard_apply_symm_apply (q : LeftQuotient (upperUnipotent (t + 1) R)) :
    lowerToStandard h R ((lowerToStandard h R).symm q) = q :=
  (lowerToStandard h R).apply_symm_apply q

/-- Right multiplication on representatives: `lowerToStandard [x g] = [(C x) g]`. -/
theorem lowerToStandard_mk_mul (x g : GeneralLinear (t + 1) R) :
    lowerToStandard h R (Quotient.mk _ (x * g)) =
      Quotient.mk _ (blockRotation h R * x * g) := by
  rw [lowerToStandard_mk, mul_assoc]

end Quotient

section FieldQuotient

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (K : Type uF) [Field K]

/-- Over a field, the codomain of `lowerToStandard` is the published
`LeftUnipotentQuotient t K = N_(t+1) \ GL_(t+1)(K)`. -/
def lowerToLeftUnipotentQuotient : LowerQuotient h K ≃ LeftUnipotentQuotient t K :=
  lowerToStandard h K

theorem lowerToLeftUnipotentQuotient_eq :
    ⇑(lowerToLeftUnipotentQuotient h K) = lowerToStandard h K :=
  rfl

@[simp]
theorem lowerToLeftUnipotentQuotient_mk (g : GeneralLinear (t + 1) K) :
    lowerToLeftUnipotentQuotient h K (Quotient.mk _ g) =
      Quotient.mk _ (blockRotation h K * g) :=
  rfl

@[simp]
theorem lowerToLeftUnipotentQuotient_symm_mk (g : GeneralLinear (t + 1) K) :
    (lowerToLeftUnipotentQuotient h K).symm (Quotient.mk _ g) =
      Quotient.mk _ ((blockRotation h K)⁻¹ * g) :=
  lowerToStandard_symm_mk h K g

end FieldQuotient

section QuotientTopology

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (R : Type uR) [CommRing R]
variable [TopologicalSpace R] [IsTopologicalRing R]

/-- `lowerToStandard` as a homeomorphism of the quotient topologies. -/
def lowerToStandardHomeomorph :
    LowerQuotient h R ≃ₜ LeftQuotient (upperUnipotent (t + 1) R) :=
  Homeomorph.Quotient.congr (Homeomorph.mulLeft (blockRotation h R))
    (rightRel_iff_blockRotation_mul h R)

@[simp]
theorem lowerToStandardHomeomorph_toEquiv :
    (lowerToStandardHomeomorph h R).toEquiv = lowerToStandard h R :=
  rfl

@[simp]
theorem lowerToStandardHomeomorph_apply (q : LowerQuotient h R) :
    lowerToStandardHomeomorph h R q = lowerToStandard h R q :=
  rfl

theorem continuous_lowerToStandard : Continuous (lowerToStandard h R) :=
  (lowerToStandardHomeomorph h R).continuous

theorem continuous_lowerToStandard_symm : Continuous (lowerToStandard h R).symm :=
  (lowerToStandardHomeomorph h R).symm.continuous

/-- `lowerToStandard` intertwines right translation by every `g ∈ GL_(t+1)(R)`. -/
theorem lowerToStandard_rightTranslate (g : GeneralLinear (t + 1) R) (q : LowerQuotient h R) :
    lowerToStandard h R (rightTranslate _ g q) =
      rightTranslate _ g (lowerToStandard h R q) := by
  induction q using Quotient.inductionOn with
  | h x => exact lowerToStandard_mk_mul h R x g

theorem lowerToStandard_symm_rightTranslate (g : GeneralLinear (t + 1) R)
    (q : LeftQuotient (upperUnipotent (t + 1) R)) :
    (lowerToStandard h R).symm (rightTranslate _ g q) =
      rightTranslate _ g ((lowerToStandard h R).symm q) := by
  rw [Equiv.symm_apply_eq, lowerToStandard_rightTranslate, Equiv.apply_symm_apply]

/-- `H⁻ \ GL_(t+1)` is Hausdorff over a Hausdorff topological ring. -/
theorem t2Space_lowerQuotient [T2Space R] : T2Space (LowerQuotient h R) :=
  leftQuotient_t2Space _ (isClosed_lowerBlockUnipotent h R)

end QuotientTopology

section QuotientCanonical

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- For the canonical p-adic topology, `H⁻ \ GL_(t+1)(F) ≃ₜ N_(t+1) \ GL_(t+1)(F)`. -/
def canonicalLowerToStandardHomeomorph :
    letI := F.canonicalTopologicalData.topology
    LowerQuotient h F.Carrier ≃ₜ LeftUnipotentQuotient t F.Carrier :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
  lowerToStandardHomeomorph h F.Carrier

@[simp]
theorem canonicalLowerToStandardHomeomorph_apply :
    letI := F.canonicalTopologicalData.topology
    ∀ q : LowerQuotient h F.Carrier,
      canonicalLowerToStandardHomeomorph F h q = lowerToStandard h F.Carrier q := by
  intro q
  rfl

/-- `H⁻ \ GL_(t+1)(F)` is Hausdorff for the canonical p-adic topology. -/
theorem t2Space_lowerQuotient_canonical :
    letI := F.canonicalTopologicalData.topology
    T2Space (LowerQuotient h F.Carrier) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  exact leftQuotient_t2Space _ (isClosed_lowerBlockUnipotent_canonical F h)

/-- For the canonical p-adic topology, `lowerToStandard` intertwines right translation. -/
theorem lowerToStandard_rightTranslate_canonical :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    ∀ (g : GeneralLinear (t + 1) F.Carrier) (q : LowerQuotient h F.Carrier),
      lowerToStandard h F.Carrier (rightTranslate _ g q) =
        rightTranslate _ g (lowerToStandard h F.Carrier q) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  intro g q
  induction q using Quotient.inductionOn with
  | h x => exact lowerToStandard_mk_mul h F.Carrier x g

end QuotientCanonical

/-! ### The lower character -/

section Character

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) {R : Type uR} [CommRing R]

/-- The first-superdiagonal sum of `C g C⁻¹`, written in the original block coordinates:
the two internal superdiagonal sums of the diagonal blocks and the corner entry in the last
row of the second block and the first column of the first block. -/
theorem sum_superdiagonal_conj_blockRotation (g : GeneralLinear (t + 1) R) :
    ∑ k : Fin t, (blockRotation h R * g * (blockRotation h R)⁻¹) k.castSucc k.succ =
      (∑ j : Fin (m 0), g ((succBlockShape m h).index 0 j.castSucc)
          ((succBlockShape m h).index 0 j.succ)) +
        (∑ j : Fin (m 1), g ((succBlockShape m h).index 1 j.castSucc)
          ((succBlockShape m h).index 1 j.succ)) +
        g ((succBlockShape m h).index 1 (Fin.last (m 1))) ((succBlockShape m h).index 0 0) := by
  have h00 : ∀ x y : Fin (m 1 + 1),
      (blockRotation h R * g * (blockRotation h R)⁻¹)
          ((succBlockShape (fun i => m i.rev) (reverse_sum h)).index 0 x)
          ((succBlockShape (fun i => m i.rev) (reverse_sum h)).index 0 y) =
        g ((succBlockShape m h).index 1 x) ((succBlockShape m h).index 1 y) :=
    fun x y => blockRotation_conj_apply_reverse_index h R g 0 0 x y
  have h01 : ∀ (x : Fin (m 1 + 1)) (y : Fin (m 0 + 1)),
      (blockRotation h R * g * (blockRotation h R)⁻¹)
          ((succBlockShape (fun i => m i.rev) (reverse_sum h)).index 0 x)
          ((succBlockShape (fun i => m i.rev) (reverse_sum h)).index 1 y) =
        g ((succBlockShape m h).index 1 x) ((succBlockShape m h).index 0 y) :=
    fun x y => blockRotation_conj_apply_reverse_index h R g 0 1 x y
  have h11 : ∀ x y : Fin (m 0 + 1),
      (blockRotation h R * g * (blockRotation h R)⁻¹)
          ((succBlockShape (fun i => m i.rev) (reverse_sum h)).index 1 x)
          ((succBlockShape (fun i => m i.rev) (reverse_sum h)).index 1 y) =
        g ((succBlockShape m h).index 0 x) ((succBlockShape m h).index 0 y) :=
    fun x y => blockRotation_conj_apply_reverse_index h R g 1 1 x y
  calc ∑ k : Fin t, (blockRotation h R * g * (blockRotation h R)⁻¹) k.castSucc k.succ
      = (∑ k : Fin (m 1), (blockRotation h R * g * (blockRotation h R)⁻¹)
            ((succBlockShape (fun i => m i.rev) (reverse_sum h)).index 0 k.castSucc)
            ((succBlockShape (fun i => m i.rev) (reverse_sum h)).index 0 k.succ)) +
          (blockRotation h R * g * (blockRotation h R)⁻¹)
            ((succBlockShape (fun i => m i.rev) (reverse_sum h)).index 0 (Fin.last (m 1)))
            ((succBlockShape (fun i => m i.rev) (reverse_sum h)).index 1
              (0 : Fin (m 0 + 1))) +
          ∑ k : Fin (m 0), (blockRotation h R * g * (blockRotation h R)⁻¹)
            ((succBlockShape (fun i => m i.rev) (reverse_sum h)).index 1 k.castSucc)
            ((succBlockShape (fun i => m i.rev) (reverse_sum h)).index 1 k.succ) :=
        sum_superdiagonal_index (reverse_sum h)
          ((blockRotation h R * g * (blockRotation h R)⁻¹ : GeneralLinear (t + 1) R) :
            Matrix (Fin (t + 1)) (Fin (t + 1)) R)
    _ = _ := by
        simp only [h00, h01, h11]
        abel

variable [TopologicalSpace R]

/-- JPSS (1983), Section 4.7: the character of the lower block subgroup obtained by pulling
back the standard character of `N_N` through `h ↦ C h C⁻¹`. -/
def lowerCharacter (ψ : UnitaryAdditiveCharacter R) : lowerBlockUnipotent h R →* ℂˣ :=
  (standardCharacter ψ t).comp (conjugationEquiv h R).toMonoidHom

@[simp]
theorem lowerCharacter_apply (ψ : UnitaryAdditiveCharacter R) (g : lowerBlockUnipotent h R) :
    lowerCharacter h ψ g = standardCharacter ψ t (conjugationEquiv h R g) :=
  rfl

/-- Evaluation: the additive character of the first-superdiagonal sum of `C h C⁻¹`. -/
theorem lowerCharacter_apply_coe (ψ : UnitaryAdditiveCharacter R) (g : lowerBlockUnipotent h R) :
    (lowerCharacter h ψ g : ℂ) =
      ψ.complex (∑ k : Fin t,
        (blockRotation h R * (g : GeneralLinear (t + 1) R) * (blockRotation h R)⁻¹)
          k.castSucc k.succ) := by
  rw [lowerCharacter_apply, standardCharacter_apply, conjugationEquiv_apply_val]

@[simp]
theorem norm_lowerCharacter (ψ : UnitaryAdditiveCharacter R) (g : lowerBlockUnipotent h R) :
    ‖(lowerCharacter h ψ g : ℂ)‖ = 1 :=
  norm_standardCharacter ψ t _

/-- The block-coordinate formula: the value of the lower character is the additive character
of the two internal superdiagonal sums and of the corner entry in the last row of the second
block and the first column of the first block. -/
theorem lowerCharacter_apply_blocks (ψ : UnitaryAdditiveCharacter R)
    (g : lowerBlockUnipotent h R) :
    (lowerCharacter h ψ g : ℂ) =
      ψ.complex (
        (∑ j : Fin (m 0), (g : GeneralLinear (t + 1) R)
          ((succBlockShape m h).index 0 j.castSucc) ((succBlockShape m h).index 0 j.succ)) +
        (∑ j : Fin (m 1), (g : GeneralLinear (t + 1) R)
          ((succBlockShape m h).index 1 j.castSucc) ((succBlockShape m h).index 1 j.succ)) +
        (g : GeneralLinear (t + 1) R) ((succBlockShape m h).index 1 (Fin.last (m 1)))
          ((succBlockShape m h).index 0 0)) := by
  rw [lowerCharacter_apply_coe, sum_superdiagonal_conj_blockRotation]

/-- Block-factor form with quantified block representatives: if the diagonal blocks of
`g = [[n_a, 0], [x, n_b]]` are `n 0 = n_a` and `n 1 = n_b`, the value of the lower character
is `θ_a(n_a) θ_b(n_b) ψ(x(last, first))`. -/
theorem lowerCharacter_eq_of_blocks (ψ : UnitaryAdditiveCharacter R)
    (g : lowerBlockUnipotent h R) (n : TwoBlockUnipotentQuotient.BlockUnipotents m R)
    (hn : ∀ (i : Fin 2) (x y : Fin (m i + 1)),
      (g : GeneralLinear (t + 1) R) ((succBlockShape m h).index i x)
        ((succBlockShape m h).index i y) =
      ((n i : upperUnipotent (m i + 1) R) : GeneralLinear (m i + 1) R) x y) :
    (lowerCharacter h ψ g : ℂ) =
      (standardCharacter ψ (m 0) (n 0) : ℂ) * (standardCharacter ψ (m 1) (n 1) : ℂ) *
        ψ.complex ((g : GeneralLinear (t + 1) R)
          ((succBlockShape m h).index 1 (Fin.last (m 1))) ((succBlockShape m h).index 0 0)) := by
  rw [lowerCharacter_apply_blocks, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
    standardCharacter_apply, standardCharacter_apply]
  simp only [hn]

/-- Block-factor form with the actual diagonal blocks of `g`. -/
theorem lowerCharacter_eq_diagonalBlocks (ψ : UnitaryAdditiveCharacter R)
    (g : lowerBlockUnipotent h R) :
    (lowerCharacter h ψ g : ℂ) =
      (standardCharacter ψ (m 0) (diagonalBlocks h R g 0) : ℂ) *
        (standardCharacter ψ (m 1) (diagonalBlocks h R g 1) : ℂ) *
        ψ.complex ((g : GeneralLinear (t + 1) R)
          ((succBlockShape m h).index 1 (Fin.last (m 1))) ((succBlockShape m h).index 0 0)) :=
  lowerCharacter_eq_of_blocks h ψ g (diagonalBlocks h R g)
    (fun i x y => (diagonalBlocks_apply h R g i x y).symm)

variable [IsTopologicalRing R]

/-- The lower character as a continuous homomorphism into `ℂˣ`. -/
def lowerCharacterContinuous (ψ : UnitaryAdditiveCharacter R) :
    ContinuousMonoidHom (lowerBlockUnipotent h R) ℂˣ where
  toMonoidHom := lowerCharacter h ψ
  continuous_toFun :=
    (standardCharacterContinuous ψ t).continuous.comp (continuous_conjugationEquiv h R)

@[simp]
theorem lowerCharacterContinuous_toMonoidHom (ψ : UnitaryAdditiveCharacter R) :
    (lowerCharacterContinuous h ψ).toMonoidHom = lowerCharacter h ψ :=
  rfl

theorem continuous_lowerCharacter (ψ : UnitaryAdditiveCharacter R) :
    Continuous (lowerCharacter h ψ) :=
  (lowerCharacterContinuous h ψ).continuous

end Character

section CanonicalCharacter

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The lower character as a continuous homomorphism for the canonical p-adic topology. -/
def canonicalLowerCharacterContinuous
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    ContinuousMonoidHom (lowerBlockUnipotent h F.Carrier) ℂˣ :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
  lowerCharacterContinuous h ψ

/-- Continuity of the lower character for the canonical p-adic topology. -/
theorem continuous_lowerCharacter_canonical
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    Continuous (lowerCharacter h ψ) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  exact continuous_lowerCharacter h ψ

end CanonicalCharacter

/-! ### Determinant order and slices of the lower quotient -/

section Padic

section Determinant

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (R : Type uR) [CommRing R]

/-- The determinant of the block rotation is the sign of the block-reversal permutation. -/
theorem determinant_blockRotation :
    (GeneralLinear.determinant (blockRotation h R) : R) =
      ((Equiv.Perm.sign (succBlockShape m h).reversePermutation : ℤ) : R) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, blockRotation_eq_permutation]
  simp only [permutation_coe, Matrix.det_permutation, Equiv.Perm.sign_inv,
    Equiv.Perm.sign_symm]

theorem determinant_blockRotation_mul_self :
    (GeneralLinear.determinant (blockRotation h R) : R) *
        (GeneralLinear.determinant (blockRotation h R) : R) = 1 := by
  rw [determinant_blockRotation, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self,
    Units.val_one, Int.cast_one]

end Determinant

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- `ord(det C) = 0` for the normalized order of the canonical p-adic structure. -/
theorem ord_determinant_blockRotation :
    F.canonicalTopologicalData.ord
      (GeneralLinear.determinant (blockRotation h F.Carrier) : F.Carrier) = 0 := by
  have hd := determinant_blockRotation_mul_self h F.Carrier
  have hm := F.canonicalTopologicalData.ord_mul
    (GeneralLinear.determinant (blockRotation h F.Carrier)).ne_zero
    (GeneralLinear.determinant (blockRotation h F.Carrier)).ne_zero
  rw [hd, F.canonicalTopologicalData.ord_one] at hm
  omega

/-- `|det C| = 1` for the normalized absolute value of the canonical p-adic structure. -/
theorem normalizedAbs_determinant_blockRotation :
    F.canonicalTopologicalData.normalizedAbs
      (GeneralLinear.determinant (blockRotation h F.Carrier) : F.Carrier) = 1 := by
  rw [F.canonicalTopologicalData.normalizedAbs_of_ne_zero
    (GeneralLinear.determinant (blockRotation h F.Carrier)).ne_zero,
    ord_determinant_blockRotation, neg_zero, zpow_zero]

/-- The determinant order of the lower quotient, transported through `lowerToStandard` from
the published determinant order of `N_N \ GL_N`. -/
def determinantOrder : LowerQuotient h F.Carrier → ℤ :=
  RankinSelberg.determinantOrder F.canonicalTopologicalData t ∘ lowerToStandard h F.Carrier

theorem determinantOrder_apply (q : LowerQuotient h F.Carrier) :
    determinantOrder F h q =
      RankinSelberg.determinantOrder F.canonicalTopologicalData t
        (lowerToStandard h F.Carrier q) :=
  rfl

/-- Representative law: the order of `[g]` is `ord(det g)`. -/
@[simp]
theorem determinantOrder_mk (g : GeneralLinear (t + 1) F.Carrier) :
    determinantOrder F h (Quotient.mk _ g) =
      F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) := by
  rw [determinantOrder_apply, lowerToStandard_mk, RankinSelberg.determinantOrder_mk, map_mul,
    Units.val_mul, F.canonicalTopologicalData.ord_mul
      (GeneralLinear.determinant (blockRotation h F.Carrier)).ne_zero
      (GeneralLinear.determinant g).ne_zero,
    ord_determinant_blockRotation, zero_add]

/-- The determinant slice of the lower quotient: the preimage under `lowerToStandard` of the
published slice of `N_N \ GL_N`. -/
def determinantSlice (k : ℤ) : Set (LowerQuotient h F.Carrier) :=
  lowerToStandard h F.Carrier ⁻¹' RankinSelberg.determinantSlice F.canonicalTopologicalData t k

theorem mem_determinantSlice {k : ℤ} {q : LowerQuotient h F.Carrier} :
    q ∈ determinantSlice F h k ↔
      lowerToStandard h F.Carrier q ∈
        RankinSelberg.determinantSlice F.canonicalTopologicalData t k :=
  Iff.rfl

theorem mem_determinantSlice_iff_determinantOrder {k : ℤ} {q : LowerQuotient h F.Carrier} :
    q ∈ determinantSlice F h k ↔ determinantOrder F h q = k :=
  Iff.rfl

/-- Representative condition for a slice: `ord(det g) = k`. -/
theorem mk_mem_determinantSlice {k : ℤ} {g : GeneralLinear (t + 1) F.Carrier} :
    (Quotient.mk _ g : LowerQuotient h F.Carrier) ∈ determinantSlice F h k ↔
      F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) = k := by
  rw [mem_determinantSlice_iff_determinantOrder, determinantOrder_mk]

/-- Exact slice correspondence: `lowerToStandard` maps the lower slice onto the published
slice. -/
theorem image_lowerToStandard_determinantSlice (k : ℤ) :
    lowerToStandard h F.Carrier '' determinantSlice F h k =
      RankinSelberg.determinantSlice F.canonicalTopologicalData t k :=
  (lowerToStandard h F.Carrier).image_preimage _

theorem preimage_lowerToStandard_symm_determinantSlice (k : ℤ) :
    (lowerToStandard h F.Carrier).symm ⁻¹' determinantSlice F h k =
      RankinSelberg.determinantSlice F.canonicalTopologicalData t k := by
  rw [determinantSlice, ← Set.preimage_comp, Equiv.self_comp_symm, Set.preimage_id]

theorem continuous_determinantOrder :
    letI := F.canonicalTopologicalData.topology
    Continuous (determinantOrder F h) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  refine (isQuotientMap_quotient_mk'
    (s := QuotientGroup.rightRel (lowerBlockUnipotent h F.Carrier))).continuous_iff.mpr ?_
  change Continuous (fun g : GeneralLinear (t + 1) F.Carrier =>
    determinantOrder F h (Quotient.mk _ g))
  simp only [determinantOrder_mk]
  exact (RankinSelberg.continuous_ord_units F.canonicalTopologicalData).comp
    (F.canonicalTopologicalData.generalLinearDeterminant (t + 1)).continuous

theorem isClopen_determinantSlice (k : ℤ) :
    letI := F.canonicalTopologicalData.topology
    IsClopen (determinantSlice F h k) := by
  let := F.canonicalTopologicalData.topology
  exact (isClopen_discrete ({k} : Set ℤ)).preimage (continuous_determinantOrder F h)

theorem isOpen_determinantSlice (k : ℤ) :
    letI := F.canonicalTopologicalData.topology
    IsOpen (determinantSlice F h k) := by
  let := F.canonicalTopologicalData.topology
  exact (isClopen_determinantSlice F h k).isOpen

theorem isClosed_determinantSlice (k : ℤ) :
    letI := F.canonicalTopologicalData.topology
    IsClosed (determinantSlice F h k) := by
  let := F.canonicalTopologicalData.topology
  exact (isClopen_determinantSlice F h k).isClosed

/-- Every slice is measurable for any Borel structure on the lower quotient. -/
theorem measurableSet_determinantSlice (k : ℤ) :
    letI := F.canonicalTopologicalData.topology
    ∀ [MeasurableSpace (LowerQuotient h F.Carrier)] [BorelSpace (LowerQuotient h F.Carrier)],
      MeasurableSet (determinantSlice F h k) := by
  let := F.canonicalTopologicalData.topology
  intro _ _
  exact (isOpen_determinantSlice F h k).measurableSet

theorem disjoint_determinantSlice {k l : ℤ} (hkl : k ≠ l) :
    Disjoint (determinantSlice F h k) (determinantSlice F h l) :=
  (RankinSelberg.disjoint_determinantSlice F.canonicalTopologicalData t hkl).preimage
    (lowerToStandard h F.Carrier)

theorem pairwise_disjoint_determinantSlice :
    Pairwise (Function.onFun Disjoint (determinantSlice F h)) :=
  fun _ _ hkl => disjoint_determinantSlice F h hkl

@[simp]
theorem iUnion_determinantSlice : ⋃ k, determinantSlice F h k = Set.univ := by
  simp only [determinantSlice, ← Set.preimage_iUnion, RankinSelberg.iUnion_determinantSlice,
    Set.preimage_univ]

/-- Right translation by `g` shifts the order by `ord(det g)`. -/
theorem determinantOrder_rightTranslate :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    ∀ (g : GeneralLinear (t + 1) F.Carrier) (q : LowerQuotient h F.Carrier),
      determinantOrder F h (rightTranslate _ g q) =
        determinantOrder F h q +
          F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  intro g q
  induction q using Quotient.inductionOn with
  | h x =>
    rw [rightTranslate_mk, determinantOrder_mk, determinantOrder_mk, map_mul, Units.val_mul,
      F.canonicalTopologicalData.ord_mul (GeneralLinear.determinant x).ne_zero
        (GeneralLinear.determinant g).ne_zero]

/-- Right translation by `g` maps the slice of order `k - ord(det g)` onto the slice of
order `k`. -/
theorem rightTranslate_mem_determinantSlice (k : ℤ) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    ∀ (g : GeneralLinear (t + 1) F.Carrier) (q : LowerQuotient h F.Carrier),
      rightTranslate _ g q ∈ determinantSlice F h k ↔
        q ∈ determinantSlice F h
          (k - F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier)) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  intro g q
  rw [mem_determinantSlice_iff_determinantOrder, mem_determinantSlice_iff_determinantOrder,
    determinantOrder_rightTranslate]
  omega

end Padic

end Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient
