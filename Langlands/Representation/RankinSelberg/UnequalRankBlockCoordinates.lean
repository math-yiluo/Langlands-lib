import Langlands.Representation.RankinSelberg.UnequalRankBilinearForms
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement

/-!
# Block coordinates for the unequal-rank block-zero covariance laws

The indices of `GL_N` are split as `Fin (n+1) ⊕ Fin m`, the leading block of
size `n+1` followed by the remaining `m` indices. In these coordinates the
actual embedding `diag(g, I)`, the JPSS block matrices, the block Weyl element
`blockWeylAt` and the elements of `U_(n+2,r+1)` become ordinary block matrices,
and the matrix identities behind JPSS (2.11.2) and (2.11.4) reduce to block
multiplication.
-/

noncomputable section

namespace Langlands.RankinSelberg

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis

universe uF

section Coordinates

variable {F : Type uF} [Field F] {n m N : ℕ}

/-- Block coordinates `Fin (n+1) ⊕ Fin m ≃ Fin N`: the left summand is the
leading block, the right summand the following `m` indices. -/
def blockCoords (h : n + 1 + m = N) : Fin (n + 1) ⊕ Fin m ≃ Fin N :=
  finSumFinEquiv.trans (finCongr h)

@[simp] theorem blockCoords_inl_val (h : n + 1 + m = N) (a : Fin (n + 1)) :
    (blockCoords h (Sum.inl a)).val = a.val := rfl

@[simp] theorem blockCoords_inr_val (h : n + 1 + m = N) (b : Fin m) :
    (blockCoords h (Sum.inr b)).val = n + 1 + b.val := rfl

theorem blockCoords_symm_of_lt (h : n + 1 + m = N) (i : Fin N) (hi : i.val < n + 1) :
    (blockCoords h).symm i = Sum.inl ⟨i.val, hi⟩ := by
  apply (blockCoords h).injective
  ext
  simp

theorem blockCoords_symm_of_le (h : n + 1 + m = N) (i : Fin N) (hi : n + 1 ≤ i.val) :
    (blockCoords h).symm i = Sum.inr ⟨i.val - (n + 1), by have := i.isLt; omega⟩ := by
  apply (blockCoords h).injective
  ext
  simp only [Equiv.apply_symm_apply, blockCoords_inr_val]
  omega

/-- A square matrix read in block coordinates. -/
def blockForm (h : n + 1 + m = N) (M : Matrix (Fin N) (Fin N) F) :
    Matrix (Fin (n + 1) ⊕ Fin m) (Fin (n + 1) ⊕ Fin m) F :=
  M.submatrix (blockCoords h) (blockCoords h)

omit [Field F] in
@[simp] theorem blockForm_apply (h : n + 1 + m = N) (M : Matrix (Fin N) (Fin N) F)
    (x y : Fin (n + 1) ⊕ Fin m) :
    blockForm h M x y = M (blockCoords h x) (blockCoords h y) := rfl

omit [Field F] in
theorem entry_eq_blockForm (h : n + 1 + m = N) (M : Matrix (Fin N) (Fin N) F)
    (i l : Fin N) :
    M i l = blockForm h M ((blockCoords h).symm i) ((blockCoords h).symm l) := by
  simp

theorem blockForm_mul (h : n + 1 + m = N) (M M' : Matrix (Fin N) (Fin N) F) :
    blockForm h (M * M') = blockForm h M * blockForm h M' :=
  (Matrix.submatrix_mul_equiv M M' _ _ _).symm

theorem blockForm_one (h : n + 1 + m = N) :
    blockForm h (1 : Matrix (Fin N) (Fin N) F) = 1 :=
  Matrix.submatrix_one_equiv _

omit [Field F] in
theorem blockForm_transpose (h : n + 1 + m = N) (M : Matrix (Fin N) (Fin N) F) :
    blockForm h M.transpose = (blockForm h M).transpose := rfl

omit [Field F] in
theorem blockForm_injective (h : n + 1 + m = N) :
    Function.Injective (blockForm (F := F) h) := by
  intro M M' hM
  ext i l
  rw [entry_eq_blockForm h M, entry_eq_blockForm h M', hM]

/-- Two invertible matrices with the same block form are equal. -/
theorem generalLinear_ext_blockForm (h : n + 1 + m = N) {g g' : Langlands.GeneralLinear N F}
    (hg : blockForm h g.val = blockForm h g'.val) : g = g' :=
  Units.ext (blockForm_injective h hg)

/-- A block upper-triangular matrix with unitriangular diagonal blocks is
upper unitriangular. -/
theorem upperUnitriangular_of_blockForm (h : n + 1 + m = N)
    {M : Matrix (Fin N) (Fin N) F} {P : Matrix (Fin (n + 1)) (Fin (n + 1)) F}
    {Q : Matrix (Fin (n + 1)) (Fin m) F} {S : Matrix (Fin m) (Fin m) F}
    (hM : blockForm h M = Matrix.fromBlocks P Q 0 S)
    (hP : ∀ a b, b < a → P a b = 0) (hP1 : ∀ a, P a a = 1)
    (hS : ∀ a b, b < a → S a b = 0) (hS1 : ∀ a, S a a = 1) :
    M.IsUpperTriangular ∧ ∀ i, M i i = 1 := by
  constructor
  · intro i l hli
    rw [entry_eq_blockForm h M, hM]
    by_cases hi : i.val < n + 1
    · have hl : l.val < n + 1 := lt_trans hli hi
      rw [blockCoords_symm_of_lt h i hi, blockCoords_symm_of_lt h l hl,
        Matrix.fromBlocks_apply₁₁]
      exact hP _ _ (by rw [Fin.lt_def]; exact hli)
    · rw [blockCoords_symm_of_le h i (by omega)]
      by_cases hl : l.val < n + 1
      · rw [blockCoords_symm_of_lt h l hl, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      · rw [blockCoords_symm_of_le h l (by omega), Matrix.fromBlocks_apply₂₂]
        have h1 : l.val < i.val := hli
        exact hS _ _ (Fin.mk_lt_mk.mpr (by omega))
  · intro i
    rw [entry_eq_blockForm h M, hM]
    by_cases hi : i.val < n + 1
    · rw [blockCoords_symm_of_lt h i hi, Matrix.fromBlocks_apply₁₁]
      exact hP1 _
    · rw [blockCoords_symm_of_le h i (by omega), Matrix.fromBlocks_apply₂₂]
      exact hS1 _

theorem blockForm_add (h : n + 1 + m = N) (M M' : Matrix (Fin N) (Fin N) F) :
    blockForm h (M + M') = blockForm h M + blockForm h M' := rfl

/-- A matrix with the entries of `diag(g, I)` has block form `[g, 0; 0, 1]`. -/
theorem blockForm_of_diagEntries (h : n + 1 + m = N) (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    {M : Matrix (Fin N) (Fin N) F}
    (hM : ∀ i l : Fin N, M i l =
      if hi : i.val < n + 1 then
        if hl : l.val < n + 1 then g ⟨i.val, hi⟩ ⟨l.val, hl⟩ else 0
      else if i = l then 1 else 0) :
    blockForm h M = Matrix.fromBlocks g 0 0 1 := by
  ext (a | b) (a' | b')
  · rw [blockForm_apply, hM, Matrix.fromBlocks_apply₁₁]
    simp [a.isLt, a'.isLt]
  · rw [blockForm_apply, hM, Matrix.fromBlocks_apply₁₂]
    have ha : (blockCoords h (Sum.inl a)).val < n + 1 := a.isLt
    have hb : ¬ (blockCoords h (Sum.inr b')).val < n + 1 := by
      simp only [blockCoords_inr_val]; omega
    rw [dite_eq_left_of_eq_true (eq_true ha), dite_eq_right_of_eq_false (eq_false hb), Matrix.zero_apply]
  · rw [blockForm_apply, hM, Matrix.fromBlocks_apply₂₁]
    have hne : blockCoords h (Sum.inr b) ≠ blockCoords h (Sum.inl a') := by
      intro he
      have := congrArg Fin.val he
      simp only [blockCoords_inr_val, blockCoords_inl_val] at this
      omega
    have hb : ¬ (blockCoords h (Sum.inr b)).val < n + 1 := by
      simp only [blockCoords_inr_val]; omega
    rw [dite_eq_right_of_eq_false (eq_false hb), Matrix.zero_apply]
    simp [hne]
  · rw [blockForm_apply, hM, Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
    have hb : ¬ (blockCoords h (Sum.inr b)).val < n + 1 := by
      simp only [blockCoords_inr_val]; omega
    rw [dite_eq_right_of_eq_false (eq_false hb)]
    simp only [(blockCoords h).injective.eq_iff, Sum.inr.injEq]

end Coordinates

section SpecificBlocks

variable {F : Type uF} [Field F] {n m : ℕ}

/-- The shared embedding `appendIdentity` is `diag(g, I)` in block coordinates. -/
theorem blockForm_appendIdentity (h : n + 1 + m = n + m + 1)
    (g : Langlands.GeneralLinear (n + 1) F) :
    blockForm h (appendIdentity n m g).val = Matrix.fromBlocks g.val 0 0 1 :=
  blockForm_of_diagEntries h g.val (appendIdentity_entry n m g)

/-- The reindexed embedding of the covariance predicate is `diag(g, I)` in
block coordinates. -/
theorem blockForm_embedding {r : ℕ} (h : n + 1 + m = r + 1)
    (g : Langlands.GeneralLinear (n + 1) F) :
    blockForm h (GeneralLinear.reindex (finCongr (show n + (r - n) + 1 = r + 1 by omega))
      (appendIdentity n (r - n) g)).val = Matrix.fromBlocks g.val 0 0 1 := by
  apply blockForm_of_diagEntries
  intro i l
  change appendIdentity n (r - n) g
      ((finCongr (show n + (r - n) + 1 = r + 1 by omega)).symm i)
      ((finCongr (show n + (r - n) + 1 = r + 1 by omega)).symm l) = _
  rw [appendIdentity_entry]
  simp only [finCongr_symm, finCongr_apply, Fin.val_cast, Fin.cast_inj]

/-- After the rank equality is substituted, the reindexed embedding is the
shared embedding itself. -/
theorem reindex_appendIdentity_eq (g : Langlands.GeneralLinear (n + 1) F) :
    GeneralLinear.reindex (finCongr (show n + (n + m - n) + 1 = n + m + 1 by omega))
      (appendIdentity n (n + m - n) g) = appendIdentity n m g := by
  have h : n + 1 + m = n + m + 1 := by omega
  apply generalLinear_ext_blockForm h
  rw [blockForm_embedding h, blockForm_appendIdentity h]

/-- The rows below the leading block of the JPSS matrix: the rows of `x`
followed by zero rows. -/
def stackRows {j : ℕ} (m : ℕ) (x : Matrix (Fin j) (Fin (n + 1)) F) :
    Matrix (Fin m) (Fin (n + 1)) F :=
  fun i b => if hi : i.val < j then x ⟨i.val, hi⟩ b else 0

theorem blockForm_rectangularEntries (j k : ℕ) (h : n + 1 + (j + k + 1) = n + (j + k + 1) + 1)
    (x : Matrix (Fin j) (Fin (n + 1)) F) :
    blockForm h (rectangularEntries j k x) =
      Matrix.fromBlocks 0 0 (stackRows (j + k + 1) x) 0 := by
  ext (a | b) (a' | b')
  · rw [blockForm_apply, Matrix.fromBlocks_apply₁₁]
    have : ¬ (n + 1 ≤ (blockCoords h (Sum.inl a)).val ∧
        (blockCoords h (Sum.inl a)).val < n + 1 + j) := by
      simp only [blockCoords_inl_val]; omega
    simp only [rectangularEntries, dite_eq_right_of_eq_false (eq_false this), Matrix.zero_apply]
  · rw [blockForm_apply, Matrix.fromBlocks_apply₁₂]
    have : ¬ (n + 1 ≤ (blockCoords h (Sum.inl a)).val ∧
        (blockCoords h (Sum.inl a)).val < n + 1 + j) := by
      simp only [blockCoords_inl_val]; omega
    simp only [rectangularEntries, dite_eq_right_of_eq_false (eq_false this), Matrix.zero_apply]
  · rw [blockForm_apply, Matrix.fromBlocks_apply₂₁]
    simp only [rectangularEntries, stackRows, blockCoords_inr_val, blockCoords_inl_val]
    by_cases hb : b.val < j
    · have ha : ¬ n < a'.val := by omega
      simp [hb, ha]
    · simp [hb]
  · rw [blockForm_apply, Matrix.fromBlocks_apply₂₂]
    have hb : ¬ (blockCoords h (Sum.inr b')).val < n + 1 := by
      simp only [blockCoords_inr_val]; omega
    simp only [rectangularEntries, dite_eq_right_of_eq_false (eq_false hb), Matrix.zero_apply]
    split_ifs <;> rfl

/-- The JPSS matrix is `[g, 0; X, 1]` in block coordinates, `X` being the
rows of `x` followed by zero rows. -/
theorem blockForm_unequalRankMatrix (j k : ℕ) (h : n + 1 + (j + k + 1) = n + (j + k + 1) + 1)
    (g : Langlands.GeneralLinear (n + 1) F) (x : Matrix (Fin j) (Fin (n + 1)) F) :
    blockForm h (unequalRankMatrix j k g x).val =
      Matrix.fromBlocks g.val 0 (stackRows (j + k + 1) x) 1 := by
  rw [unequalRankMatrix_val, blockForm_add, blockForm_appendIdentity h,
    blockForm_rectangularEntries j k h, Matrix.fromBlocks_add]
  simp

/-- The block Weyl element `diag(I, w)` in block coordinates. -/
theorem blockForm_blockWeylAt {r : ℕ} (hnr : n < r) (h : n + 1 + m = r + 1) :
    blockForm h (blockWeylAt (F := F) n r hnr).val =
      Matrix.fromBlocks 1 0 0 (weylLong m F).val := by
  have hm : r - n = m := by omega
  ext (a | b) (a' | b')
  · rw [blockForm_apply, Matrix.fromBlocks_apply₁₁]
    change blockSum ((1 : Langlands.GeneralLinear (n + 1) F), weylLong (r - n) F)
      ((finCongr _).symm (blockCoords h (Sum.inl a)))
      ((finCongr _).symm (blockCoords h (Sum.inl a'))) = _
    have e1 : (finCongr (show (n + 1) + (r - n) = r + 1 by omega)).symm
        (blockCoords h (Sum.inl a)) = Fin.castAdd (r - n) a := by ext; simp
    have e2 : (finCongr (show (n + 1) + (r - n) = r + 1 by omega)).symm
        (blockCoords h (Sum.inl a')) = Fin.castAdd (r - n) a' := by ext; simp
    rw [e1, e2, blockSum_apply_left]
    rfl
  · rw [blockForm_apply, Matrix.fromBlocks_apply₁₂]
    change blockSum ((1 : Langlands.GeneralLinear (n + 1) F), weylLong (r - n) F)
      ((finCongr _).symm (blockCoords h (Sum.inl a)))
      ((finCongr _).symm (blockCoords h (Sum.inr b'))) = _
    have e1 : (finCongr (show (n + 1) + (r - n) = r + 1 by omega)).symm
        (blockCoords h (Sum.inl a)) = Fin.castAdd (r - n) a := by ext; simp
    have e2 : (finCongr (show (n + 1) + (r - n) = r + 1 by omega)).symm
        (blockCoords h (Sum.inr b')) = Fin.natAdd (n + 1) ⟨b'.val, by omega⟩ := by ext; simp
    rw [e1, e2, blockSum_apply_left_right]
    rfl
  · rw [blockForm_apply, Matrix.fromBlocks_apply₂₁]
    change blockSum ((1 : Langlands.GeneralLinear (n + 1) F), weylLong (r - n) F)
      ((finCongr _).symm (blockCoords h (Sum.inr b)))
      ((finCongr _).symm (blockCoords h (Sum.inl a'))) = _
    have e1 : (finCongr (show (n + 1) + (r - n) = r + 1 by omega)).symm
        (blockCoords h (Sum.inr b)) = Fin.natAdd (n + 1) ⟨b.val, by omega⟩ := by ext; simp
    have e2 : (finCongr (show (n + 1) + (r - n) = r + 1 by omega)).symm
        (blockCoords h (Sum.inl a')) = Fin.castAdd (r - n) a' := by ext; simp
    rw [e1, e2, blockSum_apply_right_left]
    rfl
  · rw [blockForm_apply, Matrix.fromBlocks_apply₂₂]
    change blockSum ((1 : Langlands.GeneralLinear (n + 1) F), weylLong (r - n) F)
      ((finCongr _).symm (blockCoords h (Sum.inr b)))
      ((finCongr _).symm (blockCoords h (Sum.inr b'))) = _
    have e1 : (finCongr (show (n + 1) + (r - n) = r + 1 by omega)).symm
        (blockCoords h (Sum.inr b)) = Fin.natAdd (n + 1) ⟨b.val, by omega⟩ := by ext; simp
    have e2 : (finCongr (show (n + 1) + (r - n) = r + 1 by omega)).symm
        (blockCoords h (Sum.inr b')) = Fin.natAdd (n + 1) ⟨b'.val, by omega⟩ := by ext; simp
    rw [e1, e2, blockSum_apply_right]
    change weylLong (r - n) F _ _ = weylLong m F b b'
    rw [weylLong_entry, weylLong_entry]
    simp only [Fin.ext_iff, Fin.val_rev]
    split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)

/-- `diag(g₁, g₂)`, reindexed to the ambient rank, in block coordinates. -/
theorem blockForm_reindex_blockSum {N : ℕ} (h : n + 1 + m = N)
    (g₁ : Langlands.GeneralLinear (n + 1) F) (g₂ : Langlands.GeneralLinear m F) :
    blockForm h (GeneralLinear.reindex (finCongr h) (blockSum (g₁, g₂))).val =
      Matrix.fromBlocks g₁.val 0 0 g₂.val := by
  ext (a | b) (a' | b')
  · change blockSum (g₁, g₂) (Fin.castAdd m a) (Fin.castAdd m a') = _
    rw [blockSum_apply_left]
    rfl
  · change blockSum (g₁, g₂) (Fin.castAdd m a) (Fin.natAdd (n + 1) b') = _
    rw [blockSum_apply_left_right]
    rfl
  · change blockSum (g₁, g₂) (Fin.natAdd (n + 1) b) (Fin.castAdd m a') = _
    rw [blockSum_apply_right_left]
    rfl
  · change blockSum (g₁, g₂) (Fin.natAdd (n + 1) b) (Fin.natAdd (n + 1) b') = _
    rw [blockSum_apply_right]
    rfl

end SpecificBlocks

section Unipotent

variable {F : Type uF} [Field F] {n m r : ℕ}

/-- The lower-left block of an upper triangular matrix vanishes. -/
theorem toBlocks₂₁_blockForm_of_upper {N : ℕ} (h : n + 1 + m = N)
    {M : Matrix (Fin N) (Fin N) F} (hM : M.IsUpperTriangular) :
    (blockForm h M).toBlocks₂₁ = 0 := by
  ext a b
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, blockForm_apply, Matrix.zero_apply]
  apply hM
  have := b.isLt
  simp only [id, Fin.lt_def, blockCoords_inl_val, blockCoords_inr_val]
  omega

/-- The lower-right block of an upper unitriangular matrix is upper triangular. -/
theorem toBlocks₂₂_blockForm_lower_zero {N : ℕ} (h : n + 1 + m = N)
    {M : Matrix (Fin N) (Fin N) F} (hM : M.IsUpperTriangular) (a b : Fin m) (hab : b < a) :
    (blockForm h M).toBlocks₂₂ a b = 0 := by
  simp only [Matrix.toBlocks₂₂, Matrix.of_apply, blockForm_apply]
  apply hM
  have : b.val < a.val := hab
  simp only [id, Fin.lt_def, blockCoords_inr_val]
  omega

/-- Every element of `U_(r+1)` is block upper triangular. -/
theorem blockForm_upperUnipotent (h : n + 1 + m = r + 1) (u : upperUnipotent (r + 1) F) :
    blockForm h u.val.val = Matrix.fromBlocks (blockForm h u.val.val).toBlocks₁₁
      (blockForm h u.val.val).toBlocks₁₂ 0 (blockForm h u.val.val).toBlocks₂₂ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (blockForm h u.val.val)]
  rw [toBlocks₂₁_blockForm_of_upper h u.property.1]

/-- The leading block of an element of `U_(n+2,r+1)` is the identity. -/
theorem toBlocks₁₁_covarianceUnipotent (h : n + 1 + m = r + 1) (u : upperUnipotent (r + 1) F)
    (hu : IsUnequalRankCovarianceUnipotent n u) :
    (blockForm h u.val.val).toBlocks₁₁ = 1 := by
  ext a b
  simp only [Matrix.toBlocks₁₁, Matrix.of_apply, blockForm_apply, Matrix.one_apply]
  rw [hu _ _ (by simp only [blockCoords_inl_val]; omega) (by simp only [blockCoords_inl_val]; omega)]
  simp only [(blockCoords h).injective.eq_iff, Sum.inl.injEq]

/-- The first column of the upper-right block of an element of `U_(n+2,r+1)`
vanishes. -/
theorem toBlocks₁₂_covarianceUnipotent_zero (h : n + 1 + (m + 1) = r + 1)
    (u : upperUnipotent (r + 1) F) (hu : IsUnequalRankCovarianceUnipotent n u)
    (a : Fin (n + 1)) : (blockForm h u.val.val).toBlocks₁₂ a 0 = 0 := by
  simp only [Matrix.toBlocks₁₂, Matrix.of_apply, blockForm_apply]
  have ha := a.isLt
  rw [hu _ _ (by simp only [blockCoords_inl_val]; omega)
    (by simp only [blockCoords_inr_val, Fin.val_zero]; omega)]
  have hne : blockCoords h (Sum.inl a) ≠ blockCoords h (Sum.inr 0) := by
    intro he
    have := congrArg Fin.val he
    simp only [blockCoords_inl_val, blockCoords_inr_val] at this
    omega
  simp [hne]

/-- The first superdiagonal in block coordinates `(n+1) + (m+1)`. -/
theorem superdiag_sum_blockForm (h : n + 1 + (m + 1) = r + 1)
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) F) :
    ∑ i : Fin r, M i.castSucc i.succ =
      ∑ i : Fin n, blockForm h M (Sum.inl i.castSucc) (Sum.inl i.succ) +
        blockForm h M (Sum.inl (Fin.last n)) (Sum.inr 0) +
        ∑ i : Fin m, blockForm h M (Sum.inr i.castSucc) (Sum.inr i.succ) := by
  obtain rfl : r = n + 1 + m := by omega
  rw [Fin.sum_univ_add, Fin.sum_univ_castSucc]
  congr 1

/-- A matrix of block form `[1, Q; 0, S]` whose upper-right block has zero
first column has the superdiagonal sum of `S`. -/
theorem superdiag_sum_of_blockForm (h : n + 1 + (m + 1) = r + 1)
    {M : Matrix (Fin (r + 1)) (Fin (r + 1)) F} {Q : Matrix (Fin (n + 1)) (Fin (m + 1)) F}
    {S : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hM : blockForm h M = Matrix.fromBlocks 1 Q 0 S) (hQ : ∀ a, Q a 0 = 0) :
    ∑ i : Fin r, M i.castSucc i.succ = ∑ i : Fin m, S i.castSucc i.succ := by
  rw [superdiag_sum_blockForm h M, hM]
  simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, hQ,
    add_zero]
  rw [Finset.sum_eq_zero fun i _ => Matrix.one_apply_ne (show i.castSucc < i.succ from Fin.castSucc_lt_succ).ne, zero_add]

end Unipotent

section Identities

variable {F : Type uF} [Field F] {n : ℕ}

theorem stackRows_mul {j : ℕ} (m : ℕ) (x : Matrix (Fin j) (Fin (n + 1)) F)
    (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F) :
    stackRows m x * g = stackRows m (x * g) := by
  ext i b
  by_cases hi : i.val < j <;> simp [stackRows, Matrix.mul_apply, hi]

/-- Right translation by `diag(g, I)` acts on both JPSS variables. -/
theorem unequalRankMatrix_mul_appendIdentity (j k : ℕ) (a g : Langlands.GeneralLinear (n + 1) F)
    (x : Matrix (Fin j) (Fin (n + 1)) F) :
    unequalRankMatrix j k a x * appendIdentity n (j + k + 1) g =
      unequalRankMatrix j k (a * g) (x * g.val) := by
  have hN : n + 1 + (j + k + 1) = n + (j + k + 1) + 1 := by omega
  apply generalLinear_ext_blockForm hN
  rw [Units.val_mul, blockForm_mul, blockForm_unequalRankMatrix j k hN,
    blockForm_appendIdentity hN, blockForm_unequalRankMatrix j k hN, Matrix.fromBlocks_multiply]
  simp [stackRows_mul]

/-- The reindexed embedding of the covariance predicate commutes with the
inverse transpose. -/
theorem inverseTranspose_embedding {r : ℕ} (hnr : n < r) (g : Langlands.GeneralLinear (n + 1) F) :
    inverseTranspose (r + 1) F
        (GeneralLinear.reindex (finCongr (show n + (r - n) + 1 = r + 1 by omega))
          (appendIdentity n (r - n) g)) =
      GeneralLinear.reindex (finCongr (show n + (r - n) + 1 = r + 1 by omega))
        (appendIdentity n (r - n) (inverseTranspose (n + 1) F g)) := by
  have h : n + 1 + (r - n) = r + 1 := by omega
  apply generalLinear_ext_blockForm h
  rw [inverseTranspose_coe, ← map_inv, ← map_inv, blockForm_transpose, blockForm_embedding h,
    blockForm_embedding h, Matrix.fromBlocks_transpose, inverseTranspose_coe]
  simp

/-- The block Weyl element commutes with the reindexed embedding. -/
theorem blockWeylAt_mul_embedding {r : ℕ} (hnr : n < r) (g : Langlands.GeneralLinear (n + 1) F) :
    blockWeylAt n r hnr *
        GeneralLinear.reindex (finCongr (show n + (r - n) + 1 = r + 1 by omega))
          (appendIdentity n (r - n) g) =
      GeneralLinear.reindex (finCongr (show n + (r - n) + 1 = r + 1 by omega))
          (appendIdentity n (r - n) g) * blockWeylAt n r hnr := by
  have h : n + 1 + (r - n) = r + 1 := by omega
  apply generalLinear_ext_blockForm h
  rw [Units.val_mul, Units.val_mul, blockForm_mul, blockForm_mul, blockForm_blockWeylAt hnr h,
    blockForm_embedding h, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

/-- Left multiplication by the long Weyl element reverses the rows. -/
theorem weylLong_mul_apply {m : ℕ} {α : Type*} (M : Matrix (Fin m) α F) (i : Fin m) (b : α) :
    ((weylLong m F).val * M) i b = M i.rev b := by
  rw [Matrix.mul_apply]
  simp only [weylLong_entry, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single i.rev]
  · simp
  · intro l _ hl
    rw [ite_eq_right_iff]
    intro he
    exact absurd (by rw [← he, Fin.rev_rev]) hl
  · simp

/-- JPSS (2.11.4), original family: for `u ∈ U_(n+2,r+1)`, conjugating by
`diag(g, I)` gives another element of `U_(r+1)` with the same character value. -/
theorem originalUnipotent_identity (k : ℕ) (u : upperUnipotent (n + (0 + k + 1) + 1) F)
    (hu : IsUnequalRankCovarianceUnipotent n u) (g : Langlands.GeneralLinear (n + 1) F) :
    ∃ u' : upperUnipotent (n + (0 + k + 1) + 1) F,
      (∑ i : Fin (n + (0 + k + 1)), u'.val i.castSucc i.succ) =
        (∑ i : Fin (n + (0 + k + 1)), u.val i.castSucc i.succ) ∧
      appendIdentity n (0 + k + 1) g * u.val = u'.val * appendIdentity n (0 + k + 1) g := by
  have h : n + 1 + (0 + k + 1) = n + (0 + k + 1) + 1 := by omega
  set Q := (blockForm h u.val.val).toBlocks₁₂
  set S := (blockForm h u.val.val).toBlocks₂₂
  have hQ : ∀ a, Q a 0 = 0 := toBlocks₁₂_covarianceUnipotent_zero h u hu
  have hB : blockForm h u.val.val = Matrix.fromBlocks 1 Q 0 S := by
    rw [blockForm_upperUnipotent h u, toBlocks₁₁_covarianceUnipotent h u hu]
  let v : Langlands.GeneralLinear (n + (0 + k + 1) + 1) F :=
    appendIdentity n (0 + k + 1) g * u.val * (appendIdentity n (0 + k + 1) g)⁻¹
  have hv : blockForm h v.val = Matrix.fromBlocks 1 (g.val * Q) 0 S := by
    simp only [v, Units.val_mul, blockForm_mul, hB, ← map_inv, blockForm_appendIdentity h,
      Matrix.fromBlocks_multiply]
    simp
  have hvU : v ∈ upperUnipotent (n + (0 + k + 1) + 1) F :=
    upperUnitriangular_of_blockForm h hv (fun a b hab => Matrix.one_apply_ne hab.ne')
      (fun a => Matrix.one_apply_eq a)
      (toBlocks₂₂_blockForm_lower_zero h u.property.1)
      (fun a => by
        simp only [S, Matrix.toBlocks₂₂, Matrix.of_apply, blockForm_apply]
        exact u.property.2 _)
  refine ⟨⟨v, hvU⟩, ?_, ?_⟩
  · rw [superdiag_sum_of_blockForm h hv (fun a => by simp [Matrix.mul_apply, hQ]),
      superdiag_sum_of_blockForm h hB hQ]
  · change _ = appendIdentity n (0 + k + 1) g * u.val * (appendIdentity n (0 + k + 1) g)⁻¹ *
      appendIdentity n (0 + k + 1) g
    group

/-- The block form of an element of `U_(n+2,r+1)` together with that of its
inverse: `[1, Q; 0, D]` and `[1, Q'; 0, D']` with `D D' = D' D = 1` and
vanishing first columns of `Q` and `Q'`. -/
theorem covarianceUnipotent_blocks {m : ℕ} (h : n + 1 + (m + 1) = r + 1)
    (u : upperUnipotent (r + 1) F) (hu : IsUnequalRankCovarianceUnipotent n u) :
    blockForm h u.val.val = Matrix.fromBlocks 1 (blockForm h u.val.val).toBlocks₁₂ 0
        (blockForm h u.val.val).toBlocks₂₂ ∧
      blockForm h (u⁻¹).val.val = Matrix.fromBlocks 1 (blockForm h (u⁻¹).val.val).toBlocks₁₂ 0
        (blockForm h (u⁻¹).val.val).toBlocks₂₂ ∧
      (blockForm h u.val.val).toBlocks₂₂ * (blockForm h (u⁻¹).val.val).toBlocks₂₂ = 1 ∧
      (blockForm h (u⁻¹).val.val).toBlocks₂₂ * (blockForm h u.val.val).toBlocks₂₂ = 1 := by
  have hu' : IsUnequalRankCovarianceUnipotent n u⁻¹ :=
    (unequalRankCovarianceSubgroup n r F).inv_mem hu
  have hB : blockForm h u.val.val = Matrix.fromBlocks 1 (blockForm h u.val.val).toBlocks₁₂ 0
      (blockForm h u.val.val).toBlocks₂₂ := by
    rw [blockForm_upperUnipotent h u, toBlocks₁₁_covarianceUnipotent h u hu]
    simp
  have hB' : blockForm h (u⁻¹).val.val = Matrix.fromBlocks 1
      (blockForm h (u⁻¹).val.val).toBlocks₁₂ 0 (blockForm h (u⁻¹).val.val).toBlocks₂₂ := by
    rw [blockForm_upperUnipotent h u⁻¹, toBlocks₁₁_covarianceUnipotent h u⁻¹ hu']
    simp
  have h1 : u.val.val * (u⁻¹).val.val = 1 := by
    rw [show u.val.val * (u⁻¹).val.val = (u * u⁻¹).val.val from rfl, mul_inv_cancel]
    rfl
  have h2 : (u⁻¹).val.val * u.val.val = 1 := by
    rw [show (u⁻¹).val.val * u.val.val = (u⁻¹ * u).val.val from rfl, inv_mul_cancel]
    rfl
  have e1 := congrArg (blockForm h) h1
  have e2 := congrArg (blockForm h) h2
  rw [blockForm_mul, blockForm_one, hB, hB', Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at e1 e2
  refine ⟨hB, hB', ?_, ?_⟩
  · simpa using e1.2.2.2
  · simpa using e2.2.2.2

/-- JPSS (2.11.4), inverse-transpose family. For `u ∈ U_(n+2,r+1)`, moving
`u⁻ᵗ` across the block matrix and the block Weyl element produces, on the left,
an element of `U_(r+1)` whose first-superdiagonal sum is the negative of that of
`u`, and changes the rectangular variable by an affine map `x ↦ A x + c` with
`det A = 1`. -/
theorem dualUnipotent_identity (k : ℕ) (hnr : n < n + (k + 0 + 1))
    (u : upperUnipotent (n + (k + 0 + 1) + 1) F) (hu : IsUnequalRankCovarianceUnipotent n u) :
    ∃ (n₀ : upperUnipotent (n + (k + 0 + 1) + 1) F) (A : Matrix (Fin k) (Fin k) F)
      (c : Matrix (Fin k) (Fin (n + 1)) F),
      A.det = 1 ∧
      (∑ i : Fin (n + (k + 0 + 1)), n₀.val i.castSucc i.succ) =
        -(∑ i : Fin (n + (k + 0 + 1)), u.val i.castSucc i.succ) ∧
      ∀ (g : Langlands.GeneralLinear (n + 1) F) (x : Matrix (Fin k) (Fin (n + 1)) F),
        unequalRankMatrix k 0 g x * blockWeylAt n (n + (k + 0 + 1)) hnr *
            inverseTranspose (n + (k + 0 + 1) + 1) F u.val =
          n₀.val * unequalRankMatrix k 0 g (A * x + c) * blockWeylAt n (n + (k + 0 + 1)) hnr := by
  have h : n + 1 + (k + 0 + 1) = n + (k + 0 + 1) + 1 := by omega
  obtain ⟨hB, hB', hDD', hD'D⟩ := covarianceUnipotent_blocks h u hu
  have hu' : IsUnequalRankCovarianceUnipotent n u⁻¹ :=
    (unequalRankCovarianceSubgroup n (n + (k + 0 + 1)) F).inv_mem hu
  set Q := (blockForm h u.val.val).toBlocks₁₂
  set D := (blockForm h u.val.val).toBlocks₂₂
  set Q' := (blockForm h (u⁻¹).val.val).toBlocks₁₂
  set D' := (blockForm h (u⁻¹).val.val).toBlocks₂₂
  have hQ : ∀ a, Q a 0 = 0 := toBlocks₁₂_covarianceUnipotent_zero h u hu
  have hQ' : ∀ a, Q' a 0 = 0 := toBlocks₁₂_covarianceUnipotent_zero h u⁻¹ hu'
  -- The lower-right block `D` as an element of `U_(k+1)`.
  let Dunip : upperUnipotent (k + 0 + 1) F :=
    ⟨⟨D, D', hDD', hD'D⟩, fun a b hab => toBlocks₂₂_blockForm_lower_zero h u.property.1 a b hab,
      fun a => by
        change (blockForm h u.val.val).toBlocks₂₂ a a = 1
        simp only [Matrix.toBlocks₂₂, Matrix.of_apply, blockForm_apply]
        exact u.property.2 _⟩
  let N : upperUnipotent (k + 0 + 1) F := reflectedUnipotent Dunip
  let V : upperUnipotent (k + 0 + 1) F := N⁻¹
  have hww : (weylLong (k + 0 + 1) F).val * (weylLong (k + 0 + 1) F).val = 1 := by
    change ((weylLong (k + 0 + 1) F) * weylLong (k + 0 + 1) F).val = 1
    rw [weylLong_mul_self]
    rfl
  have hNw : N.val.val * (weylLong (k + 0 + 1) F).val = (weylLong (k + 0 + 1) F).val * D'.transpose := by
    change (weylLong (k + 0 + 1) F).val * (inverseTranspose (k + 0 + 1) F Dunip.val).val *
      (weylLong (k + 0 + 1) F).val * (weylLong (k + 0 + 1) F).val = (weylLong (k + 0 + 1) F).val * D'.transpose
    rw [mul_assoc _ (weylLong (k + 0 + 1) F).val (weylLong (k + 0 + 1) F).val, hww, mul_one, inverseTranspose_coe]
    rfl
  have hNV : N.val.val * V.val.val = 1 := by
    rw [show N.val.val * V.val.val = (N * V).val.val from rfl, mul_inv_cancel]
    rfl
  have hVup : ∀ a b : Fin (k + 0 + 1), b < a → V.val.val a b = 0 :=
    fun a b hab => V.property.1 hab
  have hVdiag : ∀ a, V.val.val a a = 1 := V.property.2
  let A : Matrix (Fin k) (Fin k) F := fun i l => V.val.val i.castSucc l.castSucc
  let c : Matrix (Fin k) (Fin (n + 1)) F := fun i b => (V.val.val * ((weylLong (k + 0 + 1) F).val * Q'.transpose)) i.castSucc b
  -- The new rectangular variable, as rows below the leading block.
  have hstack : ∀ x : Matrix (Fin k) (Fin (n + 1)) F,
      stackRows (k + 0 + 1) (A * x + c) =
        V.val.val * (stackRows (k + 0 + 1) x + (weylLong (k + 0 + 1) F).val * Q'.transpose) := by
    intro x
    ext i b
    induction i using Fin.lastCases with
    | last =>
      show stackRows (k + 0 + 1) (A * x + c) (Fin.last (k + 0)) b =
        (V.val.val * (stackRows (k + 0 + 1) x + (weylLong (k + 0 + 1) F).val * Q'.transpose))
          (Fin.last (k + 0)) b
      have hl : stackRows (k + 0 + 1) (A * x + c) (Fin.last (k + 0)) b = 0 :=
        dite_eq_right_iff.mpr fun h => absurd h (by simp)
      rw [hl, Matrix.mul_apply, Finset.sum_eq_single (Fin.last (k + 0))]
      · rw [hVdiag, one_mul, Matrix.add_apply, weylLong_mul_apply, Fin.rev_last]
        simp [stackRows, hQ']
      · intro l _ hl'
        exact mul_eq_zero_of_left (hVup _ _ (Fin.lt_last_iff_ne_last.mpr hl')) _
      · simp
    | cast i =>
      simp only [stackRows, Fin.val_castSucc, i.isLt, dite_true, Matrix.add_apply]
      rw [Matrix.mul_add, Matrix.add_apply]
      congr 1
      rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_castSucc]
      simp [A, stackRows]
  -- `det A = 1`: `A` is upper unitriangular.
  have hA : A.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular]
    · exact Finset.prod_eq_one fun i _ => hVdiag _
    · intro i l hli
      exact hVup _ _ (Fin.castSucc_lt_castSucc_iff.mpr hli)
  -- The left factor `diag(1, N)`.
  have hn₀B : blockForm h (GeneralLinear.reindex (finCongr h)
      (blockSum ((1 : Langlands.GeneralLinear (n + 1) F), N.val))).val =
      Matrix.fromBlocks 1 0 0 N.val.val := blockForm_reindex_blockSum h _ _
  have hn₀U : GeneralLinear.reindex (finCongr h)
      (blockSum ((1 : Langlands.GeneralLinear (n + 1) F), N.val)) ∈
        upperUnipotent (n + (k + 0 + 1) + 1) F :=
    upperUnitriangular_of_blockForm h hn₀B (fun a b hab => Matrix.one_apply_ne hab.ne')
      (fun a => Matrix.one_apply_eq a) (fun a b hab => N.property.1 hab) N.property.2
  refine ⟨⟨_, hn₀U⟩, A, c, hA, ?_, ?_⟩
  · rw [superdiag_sum_of_blockForm h hn₀B (fun a => rfl), superdiag_sum_of_blockForm h hB hQ]
    exact reflectedUnipotent_sum Dunip
  · intro g x
    apply generalLinear_ext_blockForm h
    have hit : blockForm h (inverseTranspose (n + (k + 0 + 1) + 1) F u.val).val =
        Matrix.fromBlocks 1 0 Q'.transpose D'.transpose := by
      rw [inverseTranspose_coe, blockForm_transpose]
      change (blockForm h (u⁻¹).val.val).transpose = _
      rw [hB', Matrix.fromBlocks_transpose]
      simp
    simp only [Units.val_mul, blockForm_mul, blockForm_unequalRankMatrix k 0 h,
      blockForm_blockWeylAt hnr h, hit, hn₀B, Matrix.fromBlocks_multiply]
    change Matrix.fromBlocks _ _ _ _ = Matrix.fromBlocks _ _ _ _
    rw [hstack x]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero,
      zero_add]
    congr 1
    · rw [← Matrix.mul_assoc, hNV, Matrix.one_mul]
    · exact hNw.symm

end Identities

end Langlands.RankinSelberg
