import Langlands.Representation.RankinSelberg.TwoBlockDominantCovarianceData
import Langlands.Representation.RankinSelberg.TwoBlockDominantBlockSupport

/-! # Actual diagonal blocks in the dominant rectangular matrix -/

noncomputable section

open scoped BigOperators

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open GeneralLinear TwoBlockLowerUnipotentQuotient

universe uF

variable {K : Type uF} [Field K]
variable {t r j k : ℕ} {m : Fin 2 → ℕ}

/-- The fixed right permutation that aligns the two diagonal blocks of the
dominant matrix with their actual row positions. -/
def diagonalRightPermutation
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1)) :
    GeneralLinear (r + 1) K :=
  weylLong (r + 1) K * blockWeyl h hr

/-- Block-Weyl conjugation of an actual Levi element. -/
theorem blockWeyl_append_levi
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
    (b : (succBlockShape m h).Levi K) :
    blockWeyl h hr *
        append hr ((succBlockShape m h).leviEmbedding K b) * blockWeyl h hr =
      reindex (coordinates h hr)
        (BlockAlgebra.lower (C := Middle j k)
          (weylLong (m 0 + 1) K * b 0 * weylLong (m 0 + 1) K)
          (weylLong (m 1 + 1) K * b 1 * weylLong (m 1 + 1) K) 0) := by
  apply Units.ext
  ext i l
  obtain ⟨i, rfl⟩ := (coordinates h hr).surjective i
  obtain ⟨l, rfl⟩ := (coordinates h hr).surjective l
  rw [blockWeyl_conjugate_entry]
  change append hr ((succBlockShape m h).leviEmbedding K b)
      (reflectedIndex h hr i) (reflectedIndex h hr l) =
    (BlockAlgebra.lower _ _ _).val
      ((coordinates h hr).symm (coordinates h hr i))
      ((coordinates h hr).symm (coordinates h hr l))
  simp only [Equiv.symm_apply_apply, BlockAlgebra.lower_val]
  rw [append_entry]
  have hinj (i l : Coordinates (m 0 + 1) j k (m 1 + 1)) :
      reflectedIndex h hr i = reflectedIndex h hr l ↔ i = l :=
    (reflectedIndex_injective h hr).eq_iff
  rcases i with i | (i | i) <;> rcases l with l | (l | l) <;>
    simp only [reflectedIndex_A_lt, reflectedIndex_B_lt, reflectedIndex_C_not_lt,
      dite_true, dite_false, reflectedIndex_A_source, reflectedIndex_B_source] <;>
    simp [BlockAlgebra.three, hinj, Matrix.one_apply]
  · change ((succBlockShape m h).leviEmbedding K b)
      ((succBlockShape m h).index 0 i.rev) ((succBlockShape m h).index 0 l.rev) =
        (weylLong (m 0 + 1) K * b 0 * weylLong (m 0 + 1) K) i l
    rw [BlockShape.leviEmbedding_apply_same, weylLong_conjugate_entry]
  · change ((succBlockShape m h).leviEmbedding K b)
      ((succBlockShape m h).index 0 i.rev) ((succBlockShape m h).index 1 l.rev) = 0
    exact TwoBlockDeformation.leviEmbedding_index_zero_one h b _ _
  · change ((succBlockShape m h).leviEmbedding K b)
      ((succBlockShape m h).index 1 i.rev) ((succBlockShape m h).index 0 l.rev) = 0
    exact TwoBlockDeformation.leviEmbedding_index_one_zero h b _ _
  · change ((succBlockShape m h).leviEmbedding K b)
      ((succBlockShape m h).index 1 i.rev) ((succBlockShape m h).index 1 l.rev) =
        (weylLong (m 1 + 1) K * b 1 * weylLong (m 1 + 1) K) i l
    rw [BlockShape.leviEmbedding_apply_same, weylLong_conjugate_entry]

/-- The complete matrix after aligning columns, expressed in the reversed
source coordinates. -/
theorem matrix_levi_reversed_entry
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
    (b : (succBlockShape m h).Levi K)
    (x : Matrix (Fin (m 0 + 1)) (Fin k) K)
    (y : Matrix (Fin j) (Fin (m 1 + 1)) K)
    (i l : Coordinates (m 0 + 1) j k (m 1 + 1)) :
    (matrix h hr ((succBlockShape m h).leviEmbedding K b) x y *
        (diagonalRightPermutation (K := K) h hr)⁻¹)
      (coordinates h hr i).rev (coordinates h hr l).rev =
      BlockAlgebra.three
        (weylLong (m 0 + 1) K * b 0 * weylLong (m 0 + 1) K).val
        (padX j x) 0 0 1
        (padY k y * (weylLong (m 1 + 1) K * b 1 * weylLong (m 1 + 1) K).val)
        0 0 (weylLong (m 1 + 1) K * b 1 * weylLong (m 1 + 1) K).val i l := by
  have he :
      matrix h hr ((succBlockShape m h).leviEmbedding K b) x y *
          (diagonalRightPermutation (K := K) h hr)⁻¹ =
        weylLong (r + 1) K *
          reindex (coordinates h hr)
            (BlockAlgebra.upper (padX j x) (padY k y) (padX_mul_padY x y) *
              BlockAlgebra.lower (C := Middle j k)
                (weylLong (m 0 + 1) K * b 0 * weylLong (m 0 + 1) K)
                (weylLong (m 1 + 1) K * b 1 * weylLong (m 1 + 1) K) 0) *
          weylLong (r + 1) K := by
    rw [map_mul, ← blockWeyl_append_levi, matrix, diagonalRightPermutation,
      mul_inv_rev, inv_eq_of_mul_eq_one_left (weylLong_mul_self (r + 1) K),
      inv_eq_of_mul_eq_one_left (blockWeyl_mul_self h hr)]
    simp only [mul_assoc, rectangleUnipotent]
  rw [he, weylLong_conjugate_entry]
  simp only [Fin.rev_rev]
  change
    (BlockAlgebra.upper _ _ _ * BlockAlgebra.lower _ _ _).val
      ((coordinates h hr).symm (coordinates h hr i))
      ((coordinates h hr).symm (coordinates h hr l)) = _
  simp only [Equiv.symm_apply_apply, Units.val_mul,
    BlockAlgebra.upper_val, BlockAlgebra.lower_val, BlockAlgebra.three_mul,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one,
    add_zero, zero_add]

/-- Reverse the complete five-block order, including internal indices. -/
def sourceReversal (a j k b : ℕ) :
    Coordinates a j k b ≃
      ((Fin b ⊕ (Fin j ⊕ Fin 1)) ⊕ (Fin k ⊕ Fin a)) where
  toFun
    | .inl i => .inr (.inr i.rev)
    | .inr (.inl (.inl i)) => .inr (.inl i.rev)
    | .inr (.inl (.inr (.inl i))) => .inl (.inr (.inr i.rev))
    | .inr (.inl (.inr (.inr i))) => .inl (.inr (.inl i.rev))
    | .inr (.inr i) => .inl (.inl i.rev)
  invFun
    | .inl (.inl i) => .inr (.inr i.rev)
    | .inl (.inr (.inl i)) => .inr (.inl (.inr (.inr i.rev)))
    | .inl (.inr (.inr i)) => .inr (.inl (.inr (.inl i.rev)))
    | .inr (.inl i) => .inr (.inl (.inl i.rev))
    | .inr (.inr i) => .inl i.rev
  left_inv := by
    rintro (i | ((i | (i | i)) | i)) <;> simp
  right_inv := by
    rintro ((i | (i | i)) | (i | i)) <;> simp

/-- Standard coordinates on the leading block, with its singleton retained. -/
def leadingCoordinates (n j : ℕ) :
    (Fin (n + 1) ⊕ (Fin j ⊕ Fin 1)) ≃ Fin (n + (j + 0 + 1) + 1) :=
  ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv).trans
    (finCongr (by omega))

/-- Standard coordinates on the trailing lower block. -/
def trailingCoordinates (k n : ℕ) :
    (Fin k ⊕ Fin (n + 1)) ≃ Fin (k + n + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))

/-- The two exposed diagonal blocks have the actual test-group rank. -/
theorem diagonalBlocksRank
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1)) :
    (m 1 + (j + 0 + 1) + 1) + (k + m 0 + 1) = r + 1 := by
  have := TwoBlockJacquet.blockRanks_add h
  omega

/-- Consecutive standard coordinates for the exposed diagonal blocks. -/
def diagonalBlocksCoordinates
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1)) :
    ((Fin (m 1 + 1) ⊕ (Fin j ⊕ Fin 1)) ⊕
      (Fin k ⊕ Fin (m 0 + 1))) ≃ Fin (r + 1) :=
  ((Equiv.sumCongr (leadingCoordinates (m 1) j)
    (trailingCoordinates k (m 0))).trans finSumFinEquiv).trans
      (finCongr (diagonalBlocksRank h hr))

/-- The explicit reversed block coordinates are the actual long reversal. -/
theorem diagonalBlocksCoordinates_sourceReversal
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
    (i : Coordinates (m 0 + 1) j k (m 1 + 1)) :
    diagonalBlocksCoordinates h hr (sourceReversal _ _ _ _ i) =
      (coordinates h hr i).rev := by
  apply Fin.ext
  have ht := TwoBlockJacquet.blockRanks_add h
  rcases i with i | ((i | (i | i)) | i) <;>
    simp [diagonalBlocksCoordinates, leadingCoordinates, trailingCoordinates,
      sourceReversal, Fin.val_rev, position] <;> omega

/-- The actual trailing invertible matrix `[1,0;X,A]`, in block coordinates. -/
def trailingBlockUnit {a k : ℕ} (A : GeneralLinear a K)
    (X : Matrix (Fin a) (Fin k) K) :
    Matrix.GeneralLinearGroup (Fin k ⊕ Fin a) K where
  val := Matrix.fromBlocks 1 0 X A.val
  inv := Matrix.fromBlocks 1 0 (-((A⁻¹).val * X)) (A⁻¹).val
  val_inv := by
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_one,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      ← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.one_mul, add_neg_cancel,
      Matrix.fromBlocks_one]
  inv_val := by
    simp [Matrix.fromBlocks_multiply]

/-- The lower block in consecutive standard coordinates. -/
def trailingBlock {a k : ℕ} (A : GeneralLinear (a + 1) K)
    (X : Matrix (Fin (a + 1)) (Fin k) K) :
    GeneralLinear (k + a + 1) K :=
  reindex (trailingCoordinates k a) (trailingBlockUnit A X)

/-- The leading unequal-rank matrix has precisely the displayed three blocks. -/
theorem leadingBlock_entry {n j : ℕ} (B : GeneralLinear (n + 1) K)
    (Y : Matrix (Fin j) (Fin (n + 1)) K)
    (i l : Fin (n + 1) ⊕ (Fin j ⊕ Fin 1)) :
    unequalRankMatrix j 0 B Y (leadingCoordinates n j i)
      (leadingCoordinates n j l) =
        BlockAlgebra.three B.val 0 0 Y 1 0 0 0 1 i l := by
  rw [unequalRankMatrix_val]
  rcases i with i | (i | i) <;> rcases l with l | (l | l) <;>
    simp [appendIdentity_entry, rectangularEntries, leadingCoordinates,
      BlockAlgebra.three, Matrix.one_apply, Fin.ext_iff]
  all_goals split_ifs <;> first | omega | simp

/-- Reversing the second rectangle and its conjugated Levi block yields `Y*B`. -/
theorem reverse_rectangle_mul {a b : ℕ}
    (Y : Matrix (Fin a) (Fin b) K) (B : GeneralLinear b K) :
    (Y * (weylLong b K * B * weylLong b K).val).submatrix Fin.rev Fin.rev =
      Y.submatrix Fin.rev Fin.rev * B.val := by
  rw [← Matrix.submatrix_mul_equiv _ _ Fin.rev Fin.revPerm Fin.rev]
  congr 1
  ext i l
  change (weylLong b K * B * weylLong b K) i.rev l.rev = B i l
  simp only [weylLong_conjugate_entry, Fin.rev_rev]

/-- The two actual standard blocks evaluated in their displayed coordinates. -/
theorem diagonalBlocks_entry
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
    (A : GeneralLinear (m 0 + 1) K) (B : GeneralLinear (m 1 + 1) K)
    (X : Matrix (Fin (m 0 + 1)) (Fin k) K)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) K)
    (i l : (Fin (m 1 + 1) ⊕ (Fin j ⊕ Fin 1)) ⊕
      (Fin k ⊕ Fin (m 0 + 1))) :
    reindex (finCongr (diagonalBlocksRank h hr))
        (blockSum (unequalRankMatrix j 0 B Y, trailingBlock A X))
      (diagonalBlocksCoordinates h hr i) (diagonalBlocksCoordinates h hr l) =
      Matrix.fromBlocks (BlockAlgebra.three B.val 0 0 Y 1 0 0 0 1) 0 0
        (Matrix.fromBlocks 1 0 X A.val) i l := by
  rcases i with i | i <;> rcases l with l | l
  · change blockSum (_, _) ((leadingCoordinates (m 1) j i).castAdd _)
      ((leadingCoordinates (m 1) j l).castAdd _) = _
    rw [blockSum_apply_left]
    exact leadingBlock_entry B Y i l
  · change blockSum (_, _) ((leadingCoordinates (m 1) j i).castAdd _)
      ((trailingCoordinates k (m 0) l).natAdd _) = 0
    exact blockSum_apply_left_right _ _ _ _
  · change blockSum (_, _) ((trailingCoordinates k (m 0) i).natAdd _)
      ((leadingCoordinates (m 1) j l).castAdd _) = 0
    exact blockSum_apply_right_left _ _ _ _
  · change blockSum (_, _) ((trailingCoordinates k (m 0) i).natAdd _)
      ((trailingCoordinates k (m 0) l).natAdd _) = _
    rw [blockSum_apply_right]
    change (trailingBlockUnit A X).val
      ((trailingCoordinates k (m 0)).symm (trailingCoordinates k (m 0) i))
      ((trailingCoordinates k (m 0)).symm (trailingCoordinates k (m 0) l)) = _
    simp only [Equiv.symm_apply_apply]
    rfl

/-- Exact factorization of the actual dominant matrix at every actual Levi
element into a leading unequal-rank block and a trailing lower block. -/
theorem matrix_levi_diagonalBlocks
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
    (b : (succBlockShape m h).Levi K)
    (x : Matrix (Fin (m 0 + 1)) (Fin k) K)
    (y : Matrix (Fin j) (Fin (m 1 + 1)) K) :
    matrix h hr ((succBlockShape m h).leviEmbedding K b) x y *
        (diagonalRightPermutation (K := K) h hr)⁻¹ =
      reindex (finCongr (diagonalBlocksRank h hr))
        (blockSum (unequalRankMatrix j 0 (b 1)
          (y.submatrix Fin.rev Fin.rev * (b 1).val),
          trailingBlock (b 0) (x.submatrix Fin.rev Fin.rev))) := by
  apply Units.ext
  ext i l
  obtain ⟨i, rfl⟩ := ((coordinates h hr).trans Fin.revPerm).surjective i
  obtain ⟨l, rfl⟩ := ((coordinates h hr).trans Fin.revPerm).surjective l
  simp only [Equiv.trans_apply, Fin.revPerm_apply]
  rw [matrix_levi_reversed_entry,
    ← diagonalBlocksCoordinates_sourceReversal h hr i,
    ← diagonalBlocksCoordinates_sourceReversal h hr l,
    diagonalBlocks_entry, padY_mul]
  have hdiag (n : ℕ) (A : GeneralLinear n K) :
      (weylLong n K * A * weylLong n K).val = A.val.submatrix Fin.rev Fin.rev := by
    ext i l
    exact weylLong_conjugate_entry n K A i l
  have hY (i : Fin j) (l : Fin (m 1 + 1)) :
      (y * (weylLong (m 1 + 1) K * b 1 * weylLong (m 1 + 1) K).val) i l =
        (y.submatrix Fin.rev Fin.rev * (b 1).val) i.rev l.rev := by
    have he := congrArg (fun M => M i.rev l.rev) (reverse_rectangle_mul y (b 1))
    simpa only [Matrix.submatrix_apply, Fin.rev_rev] using he
  rcases i with i | ((i | (i | i)) | i) <;>
    rcases l with l | ((l | (l | l)) | l) <;>
    simp [BlockAlgebra.three, sourceReversal, padX, padY,
      hdiag, Matrix.one_apply]
  simpa only [hdiag] using hY i l

end Langlands.RankinSelberg.TwoBlockDominantRectangular
