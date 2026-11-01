import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientData
import Langlands.Representation.RankinSelberg.TwoBlockLowerUnfoldingIntegrandData
import Langlands.Representation.RankinSelberg.UnequalRankComplementaryConjugationProof
import Langlands.Representation.RankinSelberg.TwoBlockDeformationCell

/-!
# Matrix identities for the first-block row split

When the total rank is `m 0 + (m 1 + 0 + 1) + 1`, the product of the first-block
embedding `diag(v, 1)` with the lower radical whose last row vanishes is the actual
unequal-rank block matrix of the original small integral. When the total rank is
`m 0 + (0 + m 1 + 1) + 1`, the Weyl-reflected inverse transpose of the actual matrix of
the transformed small integral is the block rotation times the first-block embedding of
the Weyl-reflected inverse transpose of `v`.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockFirstBlockLaurent

open GeneralLinear TwoBlockJacquet TwoBlockFirstBlockQuotient TwoBlockLowerUnipotentQuotient
  TwoBlockLowerFirstBlockQuotient TwoBlockDeformation HarmonicAnalysis.TwoBlockRowPartialFourier

universe uR

section Original

variable {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = m 0 + (m 1 + 0 + 1) + 1)
variable {R : Type uR} [Field R]

/-- The lower radical whose rows are `y` followed by the row `x`. -/
def rowSnoc (y : Matrix (Fin (m 1)) (Fin (m 0 + 1)) R) (x : Fin (m 0 + 1) → R) :
    Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R :=
  fun i => Fin.snoc (α := fun _ => Fin (m 0 + 1) → R) (fun j => y j) x i

omit [Field R] in
@[simp]
theorem rowSnoc_castSucc (y : Matrix (Fin (m 1)) (Fin (m 0 + 1)) R) (x : Fin (m 0 + 1) → R)
    (c : Fin (m 1)) : rowSnoc y x c.castSucc = y c := by
  simp only [rowSnoc, Fin.snoc_castSucc]

omit [Field R] in
@[simp]
theorem rowSnoc_last (y : Matrix (Fin (m 1)) (Fin (m 0 + 1)) R) (x : Fin (m 0 + 1) → R) :
    rowSnoc y x (Fin.last (m 1)) = x := by
  simp only [rowSnoc, Fin.snoc_last]

/-- `diag(v, 1) R(y; 0)` is the actual unequal-rank block matrix of `(v, y)`. -/
theorem firstBlockEmbedding_mul_lowerRadical_rowSnoc (v : GeneralLinear (m 0 + 1) R)
    (y : Matrix (Fin (m 1)) (Fin (m 0 + 1)) R) :
    firstBlockEmbedding h R v * lowerRadical h R (rowSnoc y 0) =
      unequalRankMatrix (m 1) 0 v y := by
  apply ext_entryBlock h R
  · rw [entryBlock_mul, firstBlockEmbedding_apply, entryBlock_levi_zero_zero,
      entryBlock_lowerRadical_zero_zero, entryBlock_levi_zero_one, Matrix.mul_one,
      Matrix.zero_mul, add_zero]
    ext a b
    have ha := a.isLt
    have hb := b.isLt
    simp only [entryBlock, Matrix.submatrix_apply, unequalRankMatrix_val, Matrix.add_apply,
      appendIdentity_entry, rectangularEntries, val_index_zero h]
    split_ifs <;> first | omega | simp
  · rw [entryBlock_mul, firstBlockEmbedding_apply, entryBlock_levi_zero_zero,
      entryBlock_lowerRadical_zero_one, entryBlock_levi_zero_one, Matrix.mul_zero,
      Matrix.zero_mul, add_zero]
    ext a b
    have ha := a.isLt
    have hb := b.isLt
    simp only [entryBlock, Matrix.submatrix_apply, unequalRankMatrix_val, Matrix.add_apply,
      appendIdentity_entry, rectangularEntries, val_index_zero h, val_index_one h,
      Fin.ext_iff]
    split_ifs <;> first | omega | simp
  · rw [entryBlock_mul, firstBlockEmbedding_apply, entryBlock_levi_one_zero,
      entryBlock_lowerRadical_zero_zero, entryBlock_levi_one_one, Matrix.zero_mul,
      zero_add, Units.val_one, Matrix.one_mul, entryBlock_lowerRadical_one_zero]
    ext c b
    have hb := b.isLt
    by_cases hc : (c : ℕ) < m 1
    · obtain ⟨c', rfl⟩ : ∃ c' : Fin (m 1), c = c'.castSucc := ⟨⟨c, hc⟩, rfl⟩
      have hc' := c'.isLt
      rw [rowSnoc_castSucc]
      simp only [entryBlock, Matrix.submatrix_apply, unequalRankMatrix_val, Matrix.add_apply,
        appendIdentity_entry, rectangularEntries, val_index_zero h, val_index_one h, Fin.ext_iff,
        Fin.val_castSucc]
      split_ifs <;> first | omega | simp
    · obtain rfl : c = Fin.last (m 1) := Fin.ext (by have := c.isLt; simp only [Fin.val_last]; omega)
      rw [rowSnoc_last]
      simp only [entryBlock, Matrix.submatrix_apply, unequalRankMatrix_val, Matrix.add_apply,
        appendIdentity_entry, rectangularEntries, val_index_zero h, val_index_one h, Fin.ext_iff,
        Fin.val_last]
      split_ifs <;> first | omega | simp
  · rw [entryBlock_mul, firstBlockEmbedding_apply, entryBlock_levi_one_zero,
      entryBlock_lowerRadical_zero_one, entryBlock_levi_one_one, Matrix.zero_mul,
      zero_add, Units.val_one, Matrix.one_mul, entryBlock_lowerRadical_one_one]
    ext c d
    have hc := c.isLt
    have hd := d.isLt
    simp only [entryBlock, Matrix.submatrix_apply, unequalRankMatrix_val, Matrix.add_apply,
      appendIdentity_entry, rectangularEntries, val_index_one h, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | omega | simp

end Original

section General

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable {R : Type uR} [Field R]

/-- The rows `(y; x)` split additively as `(y; 0) + (0; x)`. -/
theorem rowSnoc_eq_add (y : Matrix (Fin (m 1)) (Fin (m 0 + 1)) R) (x : Fin (m 0 + 1) → R) :
    rowSnoc y x = rowSnoc y 0 + rowSnoc 0 x := by
  ext c b
  by_cases hc : (c : ℕ) < m 1
  · obtain ⟨c', rfl⟩ : ∃ c' : Fin (m 1), c = c'.castSucc := ⟨⟨c, hc⟩, rfl⟩
    simp
  · obtain rfl : c = Fin.last (m 1) :=
      Fin.ext (by have := c.isLt; simp only [Fin.val_last]; omega)
    simp

/-- `R(y; x) = R(y; 0) R(0; x)`. -/
theorem lowerRadical_rowSnoc (y : Matrix (Fin (m 1)) (Fin (m 0 + 1)) R)
    (x : Fin (m 0 + 1) → R) :
    lowerRadical h R (rowSnoc y x) =
      lowerRadical h R (rowSnoc y 0) * lowerRadical h R (rowSnoc 0 x) := by
  rw [← lowerRadical_add, ← rowSnoc_eq_add]

/-- The last row of the lower radical `R(Z)` is `(Z_last, η)`. -/
theorem lastRow_lowerRadical (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R) :
    RankinSelberg.lastRow (lowerRadical h R Z) =
      join (succBlockEquiv h) (Z (Fin.last (m 1))) (TwoBlockLowerUnfolding.eta (m 1)) := by
  funext j
  obtain ⟨s, rfl⟩ := (succBlockEquiv h).surjective j
  change lowerRadical h R Z (Fin.last t) _ = _
  rw [last_eq_index_one h]
  cases s with
  | inl a => rw [join_inl, succBlockEquiv_inl, lowerRadical_index_one_zero]
  | inr b =>
    rw [join_inr, succBlockEquiv_inr, lowerRadical_index_one_one,
      TwoBlockLowerUnfolding.eta_apply]
    by_cases hb : b = Fin.last (m 1)
    · subst hb
      simp
    · simp [hb, Ne.symm hb]

/-- `lastRow(diag(v, 1) R(Z) g) = (Z_last, η) g`. -/
theorem lastRow_firstBlockEmbedding_lowerRadical_mul (v : GeneralLinear (m 0 + 1) R)
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) R) (g : GeneralLinear (t + 1) R) :
    RankinSelberg.lastRow (firstBlockEmbedding h R v * (lowerRadical h R Z * g)) =
      Matrix.vecMul
        (join (succBlockEquiv h) (Z (Fin.last (m 1))) (TwoBlockLowerUnfolding.eta (m 1)))
        g.val := by
  rw [lastRow_firstBlockEmbedding_mul, RankinSelberg.lastRow_mul_eq_vecMul,
    lastRow_lowerRadical]

/-- `(w, η) diag(v, 1) = (w v, η)`. -/
theorem vecMul_join_eta_firstBlockEmbedding (w : Fin (m 0 + 1) → R)
    (v : GeneralLinear (m 0 + 1) R) :
    Matrix.vecMul (join (succBlockEquiv h) w (TwoBlockLowerUnfolding.eta (m 1)))
        (firstBlockEmbedding h R v).val =
      join (succBlockEquiv h) (Matrix.vecMul w v.val) (TwoBlockLowerUnfolding.eta (m 1)) := by
  have hZ : join (succBlockEquiv h) w (TwoBlockLowerUnfolding.eta (m 1)) =
      RankinSelberg.lastRow (lowerRadical h R (rowSnoc 0 w)) := by
    rw [lastRow_lowerRadical, rowSnoc_last]
  rw [hZ, ← RankinSelberg.lastRow_mul_eq_vecMul, firstBlockEmbedding_apply,
    lowerRadical_mul_leviEmbedding_blockPair, ← firstBlockEmbedding_apply,
    lastRow_firstBlockEmbedding_mul, lastRow_lowerRadical]
  congr 1
  funext b
  simp only [inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_apply, Matrix.vecMul,
    dotProduct, rowSnoc_last]

end General

section Dual

variable {K : Type uR} [Field K]

/-- Inverse transpose commutes with the standard embedding `g ↦ diag(g, I_d)`. -/
theorem inverseTranspose_appendIdentity (n d : ℕ) (g : GeneralLinear (n + 1) K) :
    inverseTranspose (n + d + 1) K (appendIdentity n d g) =
      appendIdentity n d (inverseTranspose (n + 1) K g) := by
  ext i j
  rw [inverseTranspose_entry, ← map_inv, appendIdentity_entry, appendIdentity_entry]
  split_ifs <;> first | rfl | omega

variable {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = m 0 + (0 + m 1 + 1) + 1)
  (hlt : m 0 < m 0 + (0 + m 1 + 1))

/-- The Weyl-reflected inverse transpose of the transformed small matrix:
`w_(t+1) (diag(v, I_b) diag(I_a, w_b))^ι = C diag(w_a v^ι, 1)`. -/
theorem weylLong_mul_inverseTranspose_dualMatrix (v : GeneralLinear (m 0 + 1) K)
    (x : Matrix (Fin 0) (Fin (m 0 + 1)) K) :
    weylLong (m 0 + (0 + m 1 + 1) + 1) K *
        inverseTranspose (m 0 + (0 + m 1 + 1) + 1) K
          (unequalRankMatrix 0 (m 1) v x * blockWeylAt (m 0) (m 0 + (0 + m 1 + 1)) hlt) =
      blockRotation h K *
        firstBlockEmbedding h K (weylLong (m 0 + 1) K * inverseTranspose (m 0 + 1) K v) := by
  rw [unequalRankMatrix_zero_rows, map_mul, UnequalRankComplementaryConjugationProof.blockWeylAt_eq,
    inverseTranspose_permutation, inverseTranspose_appendIdentity]
  ext k l
  rw [weylLong_mul_entry, mul_permutation_entry, blockRotation_eq_permutation,
    permutation_mul_entry, Equiv.Perm.inv_def, Equiv.symm_symm]
  obtain ⟨s, hs⟩ := (succBlockEquiv h).surjective ((succBlockShape m h).reversePermutation k)
  obtain ⟨s', rfl⟩ := (succBlockEquiv h).surjective l
  have hk : k = (succBlockShape m h).reversePermutation.symm (succBlockEquiv h s) := by
    rw [hs, Equiv.symm_apply_apply]
  subst hk
  rw [Equiv.apply_symm_apply]
  have hrev : ∀ k : Fin (m 0 + (0 + m 1 + 1) + 1),
      (k.rev : ℕ) = m 0 + (0 + m 1 + 1) - k := fun k => by rw [Fin.val_rev]; omega
  have htail : ∀ l : Fin (m 0 + (0 + m 1 + 1) + 1),
      UnequalRankComplementaryConjugationProof.tailRevPerm (m 0) (m 0 + (0 + m 1 + 1)) l =
        UnequalRankComplementaryConjugationProof.tailRev (m 0) (m 0 + (0 + m 1 + 1)) l :=
    fun _ => rfl
  rw [htail]
  cases s with
  | inl a =>
    have ha := a.isLt
    have hk : (((succBlockShape m h).reversePermutation.symm
        ((succBlockShape m h).index 0 a)).rev : ℕ) = m 0 - a := by
      rw [hrev, val_reversePermutation_symm_index_zero h]
      omega
    rw [succBlockEquiv_inl]
    cases s' with
    | inl y =>
      have hy := y.isLt
      rw [succBlockEquiv_inl, firstBlockEmbedding_index_zero_zero, weylLong_mul_entry,
        UnequalRankComplementaryConjugationProof.tailRev_of_lt _ _
          (by rw [val_index_zero h]; exact hy),
        appendIdentity_entry, dite_eq_left (by rw [hk]; omega),
        dite_eq_left (by rw [val_index_zero h]; exact hy)]
      exact congrArg₂ (fun i j => inverseTranspose (m 0 + 1) K v i j)
        (Fin.ext (by dsimp only; rw [hk, Fin.val_rev]; omega))
        (Fin.ext (by dsimp only; rw [val_index_zero h]))
    | inr y =>
      have hy := y.isLt
      have hl : ¬ ((succBlockShape m h).index 1 y : ℕ) < m 0 + 1 := by
        rw [val_index_one h]
        omega
      have hl' := UnequalRankComplementaryConjugationProof.tailRev_val_of_ge _ _ hl
      rw [succBlockEquiv_inr, firstBlockEmbedding_index_zero_one, appendIdentity_entry,
        dite_eq_left (by rw [hk]; omega), dite_eq_right (by rw [hl', val_index_one h]; omega)]
  | inr c =>
    have hc := c.isLt
    have hk : (((succBlockShape m h).reversePermutation.symm
        ((succBlockShape m h).index 1 c)).rev : ℕ) = m 0 + (0 + m 1 + 1) - c := by
      rw [hrev, val_reversePermutation_symm_index_one h]
    rw [succBlockEquiv_inr]
    cases s' with
    | inl y =>
      have hy := y.isLt
      rw [succBlockEquiv_inl, firstBlockEmbedding_index_one_zero,
        UnequalRankComplementaryConjugationProof.tailRev_of_lt _ _
          (by rw [val_index_zero h]; exact hy),
        appendIdentity_entry, dite_eq_right (by rw [hk]; omega), ite_eq_right]
      intro he
      have := congrArg Fin.val he
      rw [hk, val_index_zero h] at this
      omega
    | inr y =>
      have hy := y.isLt
      have hl : ¬ ((succBlockShape m h).index 1 y : ℕ) < m 0 + 1 := by
        rw [val_index_one h]
        omega
      have hl' := UnequalRankComplementaryConjugationProof.tailRev_val_of_ge _ _ hl
      rw [succBlockEquiv_inr, firstBlockEmbedding_index_one_one, appendIdentity_entry,
        dite_eq_right (by rw [hk]; omega)]
      by_cases hcy : c = y
      · subst hcy
        rw [ite_eq_left rfl, ite_eq_left]
        apply Fin.ext
        rw [hk, hl', val_index_one h]
        omega
      · rw [ite_eq_right hcy, ite_eq_right]
        intro he
        apply hcy
        have := congrArg Fin.val he
        rw [hk, hl', val_index_one h] at this
        apply Fin.ext
        omega

end Dual

end Langlands.RankinSelberg.TwoBlockFirstBlockLaurent
