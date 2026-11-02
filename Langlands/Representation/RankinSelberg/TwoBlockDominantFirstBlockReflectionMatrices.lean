import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockMatrices
import Langlands.Representation.RankinSelberg.TwoBlockDominantRawKernel

/-! # Actual reflected smaller matrices in the dominant first-block calculation -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantFirstBlock

open GeneralLinear TwoBlockJacquet TwoBlockFirstBlockQuotient
  TwoBlockLowerUnipotentQuotient TwoBlockLowerFirstBlockQuotient
  TwoBlockDominantRectangular.BlockAlgebra

universe uK

variable {K : Type uK} [Field K]

/-- Inverse transpose of the actual JPSS matrix, including its nonzero rows. -/
theorem blockForm_inverseTranspose_unequalRankMatrix {n : ℕ} (j k : ℕ)
    (v : GeneralLinear (n + 1) K)
    (z : Matrix (Fin j) (Fin (n + 1)) K) :
    blockForm (by omega : n + 1 + (j + k + 1) = n + (j + k + 1) + 1)
      (inverseTranspose (n + (j + k + 1) + 1) K
        (unequalRankMatrix j k v z)).val =
      Matrix.fromBlocks (inverseTranspose (n + 1) K v).val
        (-(inverseTranspose (n + 1) K v).val *
          (stackRows (j + k + 1) z).transpose) 0 1 := by
  let H : n + 1 + (j + k + 1) = n + (j + k + 1) + 1 := by omega
  let M := unequalRankMatrix j k v z
  let B : Matrix (Fin (n + 1) ⊕ Fin (j + k + 1))
      (Fin (n + 1) ⊕ Fin (j + k + 1)) K := Matrix.fromBlocks (v⁻¹).val 0
    (-stackRows (j + k + 1) z * (v⁻¹).val) 1
  have hB : blockForm H M.val * B = 1 := by
    rw [blockForm_unequalRankMatrix]
    simp [B, Matrix.fromBlocks_multiply, ← Matrix.mul_assoc, -Units.val_mul]
  have hInv : blockForm H (M⁻¹).val = B := by
    calc
      blockForm H (M⁻¹).val = blockForm H (M⁻¹).val * 1 := (mul_one _).symm
      _ = blockForm H (M⁻¹).val * (blockForm H M.val * B) := by rw [hB]
      _ = B := by
        rw [← Matrix.mul_assoc, ← blockForm_mul]
        change blockForm H (M⁻¹ * M).val * B = B
        rw [inv_mul_cancel, Units.val_one, blockForm_one, Matrix.one_mul]
  rw [inverseTranspose_coe, blockForm_transpose, hInv]
  simp [B, Matrix.fromBlocks_transpose, Matrix.transpose_mul, inverseTranspose_coe]

/-- The inverse-transpose formula is unchanged by an actual rank transport. -/
theorem blockForm_inverseTranspose_reindexed_unequalRankMatrix {n N L : ℕ} (j k : ℕ)
    (hL : j + k + 1 = L) (H : n + 1 + L = N)
    (v : GeneralLinear (n + 1) K)
    (z : Matrix (Fin j) (Fin (n + 1)) K) :
    blockForm H (inverseTranspose N K
      (GeneralLinear.reindex (finCongr (by omega))
        (unequalRankMatrix j k v z))).val =
      Matrix.fromBlocks (inverseTranspose (n + 1) K v).val
        (-(inverseTranspose (n + 1) K v).val *
          (stackRows L z).transpose) 0 1 := by
  subst L
  have hN : n + (j + k + 1) + 1 = N := by omega
  subst N
  exact blockForm_inverseTranspose_unequalRankMatrix j k v z

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable (j k : ℕ)

include h in
/-- Two blocks: the first section block and the entire complementary test tail. -/
theorem firstBlockReflectionRank :
    m 0 + 1 + ((j + k + 1) + (m 1 + 1)) =
      t + (j + k + 1) + 1 := by
  have := blockRanks_add h
  omega

private theorem reflectionBlockCoords_A (i : Fin (m 0 + 1)) :
    (blockCoords (firstBlockReflectionRank h j k)).symm
      (TwoBlockDominantRectangular.coordinates h rfl (.inl i)) = .inl i := by
  apply (blockCoords (firstBlockReflectionRank h j k)).injective
  apply Fin.ext
  simp [TwoBlockDominantRectangular.position]

private theorem reflectionBlockCoords_C
    (i : TwoBlockDominantRectangular.Middle j k) :
    (blockCoords (firstBlockReflectionRank h j k)).symm
      (TwoBlockDominantRectangular.coordinates h rfl (.inr (.inl i))) =
        .inr ⟨(TwoBlockDominantRectangular.middleCoordinates j k i).val, by
          have := (TwoBlockDominantRectangular.middleCoordinates j k i).isLt
          omega⟩ := by
  apply (blockCoords (firstBlockReflectionRank h j k)).injective
  apply Fin.ext
  rcases i with i | (i | i) <;>
    simp [TwoBlockDominantRectangular.position,
      TwoBlockDominantRectangular.middleCoordinates, Nat.add_assoc]

private theorem reflectionBlockCoords_B (i : Fin (m 1 + 1)) :
    (blockCoords (firstBlockReflectionRank h j k)).symm
      (TwoBlockDominantRectangular.coordinates h rfl (.inr (.inr i))) =
        .inr ⟨j + k + 1 + i.val, by omega⟩ := by
  apply (blockCoords (firstBlockReflectionRank h j k)).injective
  apply Fin.ext
  simp [TwoBlockDominantRectangular.position, Nat.add_assoc]

/-- The first actual upper rectangle is the transpose of the padded small rows. -/
theorem blockForm_firstRectangle
    (x : Matrix (Fin (m 0 + 1)) (Fin k) K) :
    blockForm (firstBlockReflectionRank h j k)
      (TwoBlockDominantRectangular.rectangleUnipotent h rfl x
        (0 : Matrix (Fin j) (Fin (m 1 + 1)) K)).val =
      Matrix.fromBlocks 1
        (stackRows ((j + k + 1) + (m 1 + 1)) x.transpose).transpose 0 1 := by
  ext i l
  obtain ⟨i, rfl⟩ := (blockCoords (firstBlockReflectionRank h j k)).symm.surjective i
  obtain ⟨l, rfl⟩ := (blockCoords (firstBlockReflectionRank h j k)).symm.surjective l
  obtain ⟨i, rfl⟩ := (TwoBlockDominantRectangular.coordinates h rfl).surjective
    i
  obtain ⟨l, rfl⟩ := (TwoBlockDominantRectangular.coordinates h rfl).surjective
    l
  simp only [blockForm_apply, Equiv.apply_symm_apply,
    TwoBlockDominantRectangular.rectangleUnipotent_five_entry]
  rcases i with i | ((i | (i | i)) | i) <;>
    rcases l with l | ((l | (l | l)) | l) <;>
    simp [reflectionBlockCoords_A, reflectionBlockCoords_C, reflectionBlockCoords_B,
      TwoBlockDominantRectangular.rectangleEntries, Matrix.one_apply, stackRows,
      TwoBlockDominantRectangular.middleCoordinates, Fin.ext_iff]
  all_goals
    have hi := i.isLt
    have hl := l.isLt
    omega

private theorem reflectionBlockCoords_sourceA (i : Fin (m 0 + 1)) :
    (blockCoords (firstBlockReflectionRank h j k)).symm
      (firstBlockCoordinates h j k (.inl i)) = .inl i := by
  apply (blockCoords (firstBlockReflectionRank h j k)).injective
  rw [Equiv.apply_symm_apply]
  rfl

private theorem reflectionBlockCoords_sourceB (i : Fin (m 1 + 1)) :
    (blockCoords (firstBlockReflectionRank h j k)).symm
      (firstBlockCoordinates h j k (.inr (.inl i))) =
        .inr ⟨i.val, by have := i.isLt; omega⟩ := by
  apply (blockCoords (firstBlockReflectionRank h j k)).injective
  rw [Equiv.apply_symm_apply]
  rfl

private theorem reflectionBlockCoords_sourceC (i : Fin (j + k + 1)) :
    (blockCoords (firstBlockReflectionRank h j k)).symm
      (firstBlockCoordinates h j k (.inr (.inr i))) =
        .inr ⟨m 1 + 1 + i.val, by have := i.isLt; omega⟩ := by
  apply (blockCoords (firstBlockReflectionRank h j k)).injective
  apply Fin.ext
  simp only [Equiv.apply_symm_apply, blockCoords_inr_val, firstBlockCoordinates_tail_val]
  have := blockRanks_add h
  omega

/-- The first-block inclusion has identity on the entire complementary tail. -/
theorem blockForm_append_firstBlockEmbedding
    (v : GeneralLinear (m 0 + 1) K) :
    blockForm (firstBlockReflectionRank h j k)
      (appendIdentity t (j + k + 1) (firstBlockEmbedding h K v)).val =
        Matrix.fromBlocks v.val 0 0 1 := by
  ext i l
  obtain ⟨i, rfl⟩ := (blockCoords (firstBlockReflectionRank h j k)).symm.surjective i
  obtain ⟨l, rfl⟩ := (blockCoords (firstBlockReflectionRank h j k)).symm.surjective l
  obtain ⟨i, rfl⟩ := (firstBlockCoordinates h j k).surjective i
  obtain ⟨l, rfl⟩ := (firstBlockCoordinates h j k).surjective l
  simp only [blockForm_apply, Equiv.apply_symm_apply]
  change firstBlockForm h j k
    (appendIdentity t (j + k + 1) (firstBlockEmbedding h K v)).val i l = _
  rw [firstBlockForm_append_firstBlockEmbedding]
  rcases i with i | (i | i) <;> rcases l with l | (l | l) <;>
    simp [three, reflectionBlockCoords_sourceA, reflectionBlockCoords_sourceB,
      reflectionBlockCoords_sourceC, Matrix.one_apply, Fin.ext_iff]
  all_goals have hi := i.isLt; have hl := l.isLt; omega

/-- The dominant block Weyl is `diag(w_a,w_(c+b))` in these coordinates. -/
theorem blockForm_dominant_blockWeyl :
    blockForm (firstBlockReflectionRank h j k)
      (TwoBlockDominantRectangular.blockWeyl (K := K) h rfl).val =
        Matrix.fromBlocks (weylLong (m 0 + 1) K).val 0 0
          (weylLong ((j + k + 1) + (m 1 + 1)) K).val :=
  blockForm_reindex_blockSum _ _ _

/-- Left multiplication passes through the zero-padded row transpose. -/
theorem transpose_stackRows_left_mul {a q : ℕ} (L : ℕ)
    (A : Matrix (Fin (a + 1)) (Fin (a + 1)) K)
    (z : Matrix (Fin q) (Fin (a + 1)) K) :
    (stackRows L (A * z.transpose).transpose).transpose =
      A * (stackRows L z).transpose := by
  ext i l
  by_cases hl : l.val < q <;>
    simp [stackRows, Matrix.mul_apply, hl, mul_comm]

/-- Reflection of the actual small JPSS matrix gives the first lower rectangle,
with the full complementary Weyl and the actual first-block Levi inclusion. -/
theorem firstBlock_reflection_matrix
    (v : GeneralLinear (m 0 + 1) K)
    (z : Matrix (Fin k) (Fin (m 0 + 1)) K) :
    inverseTranspose (t + (j + k + 1) + 1) K
        (GeneralLinear.reindex (finCongr (by have := blockRanks_add h; omega))
          (unequalRankMatrix k (m 1 + 1 + j)
            (weylLong (m 0 + 1) K * inverseTranspose (m 0 + 1) K v) z)) *
        blockWeylAt (m 0) (t + (j + k + 1))
          (by have := blockRanks_add h; omega) =
      TwoBlockDominantRectangular.rectangleUnipotent h rfl
          (-(weylLong (m 0 + 1) K).val * v.val * z.transpose)
          (0 : Matrix (Fin j) (Fin (m 1 + 1)) K) *
        TwoBlockDominantRectangular.blockWeyl h rfl *
        appendIdentity t (j + k + 1) (firstBlockEmbedding h K v) := by
  apply generalLinear_ext_blockForm (firstBlockReflectionRank h j k)
  simp only [Units.val_mul, blockForm_mul, blockForm_firstRectangle,
    blockForm_dominant_blockWeyl, blockForm_append_firstBlockEmbedding]
  rw [blockForm_inverseTranspose_reindexed_unequalRankMatrix k (m 1 + 1 + j)
    (by omega), blockForm_blockWeylAt]
  simp only [map_mul, inverseTranspose_weylLong, inverseTranspose_involutive,
    Units.val_mul, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.one_mul, Matrix.mul_one, zero_add, add_zero]
  rw [transpose_stackRows_left_mul]
  simp [Matrix.mul_assoc]

/-- Remaining second-block columns commute with the leading first-block inclusion. -/
theorem firstBlockRemaining_commute
    (v : GeneralLinear (m 0 + 1) K)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) K) :
    appendIdentity t (j + k + 1) (firstBlockEmbedding h K v) *
        rectangularUnipotent j k (firstBlockColumns h j 0 Y) =
      rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
        appendIdentity t (j + k + 1) (firstBlockEmbedding h K v) := by
  apply Units.ext
  apply firstBlockForm_injective h j k
  simp only [Units.val_mul, firstBlockForm_mul,
    firstBlockForm_append_firstBlockEmbedding, firstBlockForm_rectangularUnipotent]
  have hz : stackRows (j + k + 1) (0 : Matrix (Fin j) (Fin (m 0 + 1)) K) = 0 := by
    ext i l
    simp [stackRows]
  simp [hz, three_mul]

/-- Source coordinates of the reflected five-block indices, in the original first/second/tail order. -/
def firstBlockReflectedSourceCoordinates :
    TwoBlockDominantRectangular.Coordinates (m 0 + 1) j k (m 1 + 1) →
      Fin (m 0 + 1) ⊕ (Fin (m 1 + 1) ⊕ Fin (j + k + 1))
  | .inl i => .inl i.rev
  | .inr (.inl i) => .inr (.inr (TwoBlockDominantRectangular.middleCoordinates j k i).rev)
  | .inr (.inr i) => .inr (.inl i.rev)

private theorem reflectedIndex_eq_source
    (i : TwoBlockDominantRectangular.Coordinates (m 0 + 1) j k (m 1 + 1)) :
    TwoBlockDominantRectangular.reflectedIndex h rfl i =
      firstBlockCoordinates h j k (firstBlockReflectedSourceCoordinates j k i) := by
  rcases i with i | (i | i) <;> rfl

private theorem stackRows_middle_rev_k
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) K) (i : Fin k) (l : Fin (m 1 + 1)) :
    stackRows (j + k + 1) Y
      (TwoBlockDominantRectangular.middleCoordinates j k (.inl i)).rev l = 0 := by
  have hn : ¬(TwoBlockDominantRectangular.middleCoordinates j k (.inl i)).rev.val < j := by
    simp [TwoBlockDominantRectangular.middleCoordinates, Fin.val_rev]
    have := i.isLt
    omega
  rw [stackRows, dite_eq_right hn]

private theorem stackRows_middle_rev_one
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) K) (i : Fin 1) (l : Fin (m 1 + 1)) :
    stackRows (j + k + 1) Y
      (TwoBlockDominantRectangular.middleCoordinates j k (.inr (.inl i))).rev l = 0 := by
  have hn : ¬(TwoBlockDominantRectangular.middleCoordinates j k (.inr (.inl i))).rev.val < j := by
    simp [TwoBlockDominantRectangular.middleCoordinates, Fin.val_rev]
  rw [stackRows, dite_eq_right hn]

private theorem stackRows_middle_rev_j
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) K) (i : Fin j) (l : Fin (m 1 + 1)) :
    stackRows (j + k + 1) Y
      (TwoBlockDominantRectangular.middleCoordinates j k (.inr (.inr i))).rev l =
        Y i.rev l := by
  have hn : (TwoBlockDominantRectangular.middleCoordinates j k (.inr (.inr i))).rev.val < j := by
    have := i.isLt
    simp [TwoBlockDominantRectangular.middleCoordinates, Fin.val_rev]
    omega
  rw [stackRows, dite_eq_left hn]
  congr 1
  apply Fin.ext
  simp [TwoBlockDominantRectangular.middleCoordinates, Fin.val_rev]
  have := i.isLt
  omega

/-- Conjugating the remaining columns reverses both indices of the second rectangle. -/
theorem blockWeyl_firstBlockRemaining
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) K) :
    TwoBlockDominantRectangular.blockWeyl h rfl *
        rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
        TwoBlockDominantRectangular.blockWeyl h rfl =
      TwoBlockDominantRectangular.rectangleUnipotent h rfl
        (0 : Matrix (Fin (m 0 + 1)) (Fin k) K) (Y.submatrix Fin.rev Fin.rev) := by
  apply Units.ext
  ext i l
  obtain ⟨i, rfl⟩ := (TwoBlockDominantRectangular.coordinates h rfl).surjective i
  obtain ⟨l, rfl⟩ := (TwoBlockDominantRectangular.coordinates h rfl).surjective l
  rw [TwoBlockDominantRectangular.blockWeyl_conjugate_entry,
    TwoBlockDominantRectangular.rectangleUnipotent_five_entry,
    reflectedIndex_eq_source, reflectedIndex_eq_source]
  change firstBlockForm h j k
    (rectangularUnipotent j k (firstBlockColumns h j 0 Y)).val
      (firstBlockReflectedSourceCoordinates j k i) (firstBlockReflectedSourceCoordinates j k l) = _
  rw [firstBlockForm_rectangularUnipotent]
  have hz : stackRows (j + k + 1) (0 : Matrix (Fin j) (Fin (m 0 + 1)) K) = 0 := by
    ext i l
    simp [stackRows]
  rcases i with i | ((i | (i | i)) | i) <;>
    rcases l with l | ((l | (l | l)) | l) <;>
      simp [firstBlockReflectedSourceCoordinates, three, TwoBlockDominantRectangular.rectangleEntries,
        stackRows_middle_rev_k, stackRows_middle_rev_one, stackRows_middle_rev_j,
        Matrix.one_apply, (TwoBlockDominantRectangular.middleCoordinates j k).injective.eq_iff, hz]

end Langlands.RankinSelberg.TwoBlockDominantFirstBlock
