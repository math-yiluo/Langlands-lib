import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockCoordinates
import Langlands.Representation.RankinSelberg.UnequalRankBlockCoordinates
import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientData

/-! # Actual matrix bridges for the dominant first-block calculation -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantFirstBlock

open GeneralLinear TwoBlockJacquet TwoBlockFirstBlockQuotient
  TwoBlockLowerUnipotentQuotient TwoBlockLowerFirstBlockQuotient
  TwoBlockDominantRectangular.BlockAlgebra

universe uF

variable {K : Type uF} [Field K]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable (j k : ℕ)

/-- The first block, second block, and external rows with their identity tail. -/
def firstBlockCoordinates :
    (Fin (m 0 + 1) ⊕ (Fin (m 1 + 1) ⊕ Fin (j + k + 1))) ≃
      Fin (t + (j + k + 1) + 1) :=
  (Equiv.sumAssoc _ _ _).symm |>.trans
    ((Equiv.sumCongr (blockCoords (blockRanks_add h)) (Equiv.refl _)).trans
      (blockCoords (by omega : t + 1 + (j + k + 1) = t + (j + k + 1) + 1)))

@[simp] theorem firstBlockCoordinates_inl_val (i : Fin (m 0 + 1)) :
    (firstBlockCoordinates h j k (.inl i)).val = i.val := rfl

@[simp] theorem firstBlockCoordinates_middle_val (i : Fin (m 1 + 1)) :
    (firstBlockCoordinates h j k (.inr (.inl i))).val = m 0 + 1 + i.val := rfl

@[simp] theorem firstBlockCoordinates_tail_val (i : Fin (j + k + 1)) :
    (firstBlockCoordinates h j k (.inr (.inr i))).val = t + 1 + i.val := rfl

/-- The actual ambient matrix read in the three ordered blocks. -/
def firstBlockForm (M : Matrix (Fin (t + (j + k + 1) + 1))
    (Fin (t + (j + k + 1) + 1)) K) :=
  M.submatrix (firstBlockCoordinates h j k) (firstBlockCoordinates h j k)

theorem firstBlockForm_mul (M N : Matrix (Fin (t + (j + k + 1) + 1))
    (Fin (t + (j + k + 1) + 1)) K) :
    firstBlockForm h j k (M * N) = firstBlockForm h j k M * firstBlockForm h j k N :=
  (Matrix.submatrix_mul_equiv M N _ _ _).symm

theorem firstBlockForm_one :
    firstBlockForm h j k (1 : Matrix _ _ K) = 1 :=
  Matrix.submatrix_one_equiv _

omit [Field K] in
theorem firstBlockForm_injective : Function.Injective (firstBlockForm (K := K) h j k) := by
  intro M N he
  ext i l
  have hm := congrFun₂ he ((firstBlockCoordinates h j k).symm i)
    ((firstBlockCoordinates h j k).symm l)
  simpa only [firstBlockForm, Matrix.submatrix_apply, Equiv.apply_symm_apply] using hm

/-- Join the external first- and second-block columns in the actual rank `t+1`. -/
def firstBlockColumns (U : Matrix (Fin j) (Fin (m 0 + 1)) K)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) K) : Matrix (Fin j) (Fin (t + 1)) K :=
  (Matrix.fromCols U Y).submatrix id (blockCoords (blockRanks_add h)).symm

omit [Field K] in
@[simp] theorem firstBlockColumns_left (U : Matrix (Fin j) (Fin (m 0 + 1)) K)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) K) (i : Fin j) (l : Fin (m 0 + 1)) :
    firstBlockColumns h j U Y i (blockCoords (blockRanks_add h) (.inl l)) = U i l := by
  simp [firstBlockColumns]

omit [Field K] in
@[simp] theorem firstBlockColumns_right (U : Matrix (Fin j) (Fin (m 0 + 1)) K)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) K) (i : Fin j) (l : Fin (m 1 + 1)) :
    firstBlockColumns h j U Y i (blockCoords (blockRanks_add h) (.inr l)) = Y i l := by
  simp [firstBlockColumns]

private theorem blockCoords_zero (i : Fin (m 0 + 1)) :
    blockCoords (blockRanks_add h) (.inl i) = (succBlockShape m h).index 0 i := by
  rw [index_zero]
  rfl

private theorem blockCoords_one (i : Fin (m 1 + 1)) :
    blockCoords (blockRanks_add h) (.inr i) = (succBlockShape m h).index 1 i := by
  rw [index_one]
  rfl

omit [Field K] in
private theorem firstBlockForm_nested
    (M : Matrix (Fin (t + (j + k + 1) + 1)) (Fin (t + (j + k + 1) + 1)) K) :
    firstBlockForm h j k M =
      (blockForm (by omega : t + 1 + (j + k + 1) = t + (j + k + 1) + 1) M).submatrix
        ((Equiv.sumAssoc _ _ _).symm.trans
          (Equiv.sumCongr (blockCoords (blockRanks_add h)) (Equiv.refl _)))
        ((Equiv.sumAssoc _ _ _).symm.trans
          (Equiv.sumCongr (blockCoords (blockRanks_add h)) (Equiv.refl _))) := rfl

/-- The leading rank inclusion has its actual two section blocks and an identity tail. -/
theorem firstBlockForm_appendIdentity (g : GeneralLinear (t + 1) K) :
    firstBlockForm h j k (appendIdentity t (j + k + 1) g).val =
      three (entryBlock h K g 0 0) (entryBlock h K g 0 1) 0
        (entryBlock h K g 1 0) (entryBlock h K g 1 1) 0 0 0 1 := by
  rw [firstBlockForm_nested, blockForm_appendIdentity]
  ext i l
  rcases i with i | (i | i) <;> rcases l with l | (l | l) <;>
    simp [three, entryBlock, Matrix.submatrix_apply, Equiv.sumAssoc]
  all_goals simp only [blockCoords_zero h, blockCoords_one h]

/-- The actual first-block Levi inclusion becomes `diag(v,1,1)`. -/
theorem firstBlockForm_append_firstBlockEmbedding
    (v : GeneralLinear (m 0 + 1) K) :
    firstBlockForm h j k (appendIdentity t (j + k + 1)
      (firstBlockEmbedding h K v)).val = three v.val 0 0 0 1 0 0 0 1 := by
  rw [firstBlockForm_appendIdentity, firstBlockEmbedding_apply]
  simp

/-- The actual lower radical is the lower-left `Z` between the first two blocks. -/
theorem firstBlockForm_append_lowerRadical
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) K) :
    firstBlockForm h j k (appendIdentity t (j + k + 1)
      (lowerRadical h K Z)).val = three 1 0 0 Z 1 0 0 0 1 := by
  rw [firstBlockForm_appendIdentity]
  simp

/-- The external rectangle is its two column blocks, with the exact identity tail. -/
theorem firstBlockForm_rectangularUnipotent
    (U : Matrix (Fin j) (Fin (m 0 + 1)) K)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) K) :
    firstBlockForm h j k (rectangularUnipotent j k (firstBlockColumns h j U Y)).val =
      three 1 0 0 0 1 0 (stackRows (j+k+1) U) (stackRows (j+k+1) Y) 1 := by
  change firstBlockForm h j k (1 + rectangularEntries j k (firstBlockColumns h j U Y)) = _
  rw [firstBlockForm_nested, blockForm_add, blockForm_one, blockForm_rectangularEntries]
  ext i l
  rcases i with i | (i | i) <;> rcases l with l | (l | l) <;>
    simp [three, Matrix.submatrix_apply, Equiv.sumAssoc, stackRows, Matrix.one_apply]

/-- Join the section's lower-radical rows and the changed external rows. -/
def firstBlockRows
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) K)
    (T : Matrix (Fin j) (Fin (m 0 + 1)) K) :
    Matrix (Fin (m 1 + 1 + j)) (Fin (m 0 + 1)) K :=
  (Matrix.fromRows Z T).submatrix finSumFinEquiv.symm id

/-- The first-block JPSS matrix, reindexed to the original ambient rank. -/
def firstBlockSmallMatrix
    (v : GeneralLinear (m 0 + 1) K)
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) K)
    (T : Matrix (Fin j) (Fin (m 0 + 1)) K) :
    GeneralLinear (t + (j + k + 1) + 1) K :=
  GeneralLinear.reindex (finCongr (by have := blockRanks_add h; omega))
    (unequalRankMatrix (m 1 + 1 + j) k v (firstBlockRows j Z T))

omit t h in
private def firstBlockSmallCoordinates :
    (Fin (m 0 + 1) ⊕ (Fin (m 1 + 1) ⊕ Fin (j + k + 1))) ≃
      (Fin (m 0 + 1) ⊕ Fin (m 1 + 1 + j + k + 1)) :=
  Equiv.sumCongr (Equiv.refl _)
    (finSumFinEquiv.trans (finCongr (by clear h t; omega)))

private theorem firstBlockSmallCoordinates_eq
    (i : Fin (m 0 + 1) ⊕ (Fin (m 1 + 1) ⊕ Fin (j + k + 1))) :
    (finCongr (show m 0 + (m 1 + 1 + j + k + 1) + 1 =
        t + (j + k + 1) + 1 by have := blockRanks_add h; omega)).symm
        (firstBlockCoordinates h j k i) =
      blockCoords (show m 0 + 1 + (m 1 + 1 + j + k + 1) =
          m 0 + (m 1 + 1 + j + k + 1) + 1 by omega)
        (firstBlockSmallCoordinates (m := m) j k i) := by
  rcases i with i | (i | i)
  · rfl
  · rfl
  · apply Fin.ext
    change t + 1 + i.val = m 0 + 1 + (m 1 + 1 + i.val)
    have := blockRanks_add h
    omega

private theorem firstBlockForm_small_nested
    (g : GeneralLinear (m 0 + (m 1 + 1 + j + k + 1) + 1) K) :
    firstBlockForm h j k
      (GeneralLinear.reindex (finCongr (by have := blockRanks_add h; omega)) g).val =
      (blockForm (show m 0 + 1 + (m 1 + 1 + j + k + 1) =
          m 0 + (m 1 + 1 + j + k + 1) + 1 by omega) g.val).submatrix
        (firstBlockSmallCoordinates (m := m) j k)
        (firstBlockSmallCoordinates (m := m) j k) := by
  ext i l
  change g.val _ _ = g.val _ _
  rw [firstBlockSmallCoordinates_eq, firstBlockSmallCoordinates_eq]

/-- The small integral has both the Jacquet rows and the changed external rows. -/
theorem firstBlockForm_smallMatrix
    (v : GeneralLinear (m 0 + 1) K)
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) K)
    (T : Matrix (Fin j) (Fin (m 0 + 1)) K) :
    firstBlockForm h j k (firstBlockSmallMatrix h j k v Z T).val =
      three v.val 0 0 Z 1 0 (stackRows (j+k+1) T) 0 1 := by
  rw [firstBlockSmallMatrix, firstBlockForm_small_nested,
    blockForm_unequalRankMatrix]
  ext i l
  rcases i with i | (i | i) <;> rcases l with l | (l | l) <;>
    simp [firstBlockSmallCoordinates, three, Matrix.submatrix_apply, stackRows,
      firstBlockRows, Matrix.one_apply]
  · rw [dite_eq_left (by have := i.isLt; omega)]
    change (Matrix.fromRows Z T) (finSumFinEquiv.symm (Fin.castAdd j i)) l = Z i l
    simp
  · intro he
    have he' := congrArg Fin.val he
    have := i.isLt
    simp only [Fin.val_castAdd, Fin.val_natAdd] at he'
    omega
  · split_ifs with hi
    · change (Matrix.fromRows Z T)
        (finSumFinEquiv.symm (Fin.natAdd (m 1 + 1) ⟨i.val, hi⟩)) l = _
      rw [finSumFinEquiv_symm_apply_natAdd (m := m 1 + 1) ⟨i.val, hi⟩]
      rfl
    · rfl
  · intro he
    have he' := congrArg Fin.val he
    have := l.isLt
    simp only [Fin.val_castAdd, Fin.val_natAdd] at he'
    omega

/-- Actual matrix factorization for the first-block change `T = U*v + Y*Z`. -/
theorem firstBlock_matrix_factorization
    (v : GeneralLinear (m 0 + 1) K)
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) K)
    (U : Matrix (Fin j) (Fin (m 0 + 1)) K)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) K) :
    rectangularUnipotent j k (firstBlockColumns h j U Y) *
        appendIdentity t (j+k+1) (firstBlockEmbedding h K v) *
        appendIdentity t (j+k+1) (lowerRadical h K Z) =
      firstBlockSmallMatrix h j k v Z (U*v.val + Y*Z) *
        rectangularUnipotent j k (firstBlockColumns h j 0 Y) := by
  apply Units.ext
  apply firstBlockForm_injective h j k
  simp only [Units.val_mul, firstBlockForm_mul, firstBlockForm_rectangularUnipotent,
    firstBlockForm_append_firstBlockEmbedding, firstBlockForm_append_lowerRadical,
    firstBlockForm_smallMatrix]
  have hs :
      stackRows (j+k+1) (U*v.val + Y*Z) =
        stackRows (j+k+1) U * v.val + stackRows (j+k+1) Y * Z := by
    ext i l
    by_cases hi : i.val < j <;> simp [stackRows, Matrix.mul_apply, hi]
  have hz : stackRows (j+k+1) (0 : Matrix (Fin j) (Fin (m 0 + 1)) K) = 0 := by
    ext i l
    simp [stackRows]
  rw [hs, hz]
  exact firstBlock_three_factorization v.val Z (stackRows (j+k+1) U) (stackRows (j+k+1) Y)

end Langlands.RankinSelberg.TwoBlockDominantFirstBlock
