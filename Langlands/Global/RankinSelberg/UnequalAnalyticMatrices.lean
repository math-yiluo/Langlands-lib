import Langlands.Global.RankinSelberg.UnequalIntegrals

/-! # Matrix identities for the unequal-rank projection

Entry formulas for the padding `diag(g, I)`, and the facts about the radical
`Y_(n,k)` (the block unipotent subgroup for `projectionWeight n k`) used in the analytic
theory of the unequal-rank integral: its `k`-th column and last row are standard basis
vectors, it is upper unitriangular, its superdiagonal is additive, it is normalized by the
block parabolic subgroup, and conjugation by a padded matrix `diag(γ, I)` with `γ` of size at
most `k` does not change its superdiagonal. -/

noncomputable section
set_option autoImplicit false

open Langlands.Global.RankinSelbergGlobal

namespace Langlands.Global.RankinSelbergGlobal.UnequalAnalytic

section Matrix

variable {R : Type*} [CommRing R]

/-- Multiplying on the left by a matrix whose `i`-th row is a standard basis row. -/
theorem mul_apply_of_row {n : ℕ} {A : Matrix (Fin n) (Fin n) R} (B : Matrix (Fin n) (Fin n) R)
    {i : Fin n} (hA : ∀ k, A i k = (1 : Matrix (Fin n) (Fin n) R) i k) (j : Fin n) :
    (A * B) i j = B i j := by
  rw [Matrix.mul_apply]
  simp only [hA, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

/-- Multiplying on the right by a matrix whose `j`-th column is a standard basis column. -/
theorem mul_apply_of_col {n : ℕ} (A : Matrix (Fin n) (Fin n) R) {B : Matrix (Fin n) (Fin n) R}
    {j : Fin n} (hB : ∀ k, B k j = (1 : Matrix (Fin n) (Fin n) R) k j) (i : Fin n) :
    (A * B) i j = A i j := by
  rw [Matrix.mul_apply]
  simp only [hB, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

private theorem finSumFinEquiv_symm_cast_of_lt {m n : ℕ} (h : m + (n - m) = n) (i : Fin n)
    (hi : (i : ℕ) < m) :
    finSumFinEquiv.symm ((finCongr h).symm i) = Sum.inl ⟨i, hi⟩ := by
  rw [Equiv.symm_apply_eq]
  ext
  simp

private theorem finSumFinEquiv_symm_cast_of_le {m n : ℕ} (h : m + (n - m) = n) (i : Fin n)
    (hi : m ≤ (i : ℕ)) :
    finSumFinEquiv.symm ((finCongr h).symm i) = Sum.inr ⟨i - m, by omega⟩ := by
  rw [Equiv.symm_apply_eq]
  ext
  simp
  omega

/-- **Entries of `diag(M, I)`.** -/
theorem padGL_apply {m n : ℕ} (h : m ≤ n) (M : Matrix.GeneralLinearGroup (Fin m) R)
    (i j : Fin n) :
    (padGL h M : Matrix (Fin n) (Fin n) R) i j =
      if hij : (i : ℕ) < m ∧ (j : ℕ) < m then (M : Matrix (Fin m) (Fin m) R) ⟨i, hij.1⟩ ⟨j, hij.2⟩
      else (1 : Matrix (Fin n) (Fin n) R) i j := by
  have e1 : (padGL h M : Matrix (Fin n) (Fin n) R) i j =
      Matrix.fromBlocks (M : Matrix (Fin m) (Fin m) R) 0 0
        (1 : Matrix (Fin (n - m)) (Fin (n - m)) R)
        (finSumFinEquiv.symm ((finCongr (Nat.add_sub_of_le h)).symm i))
        (finSumFinEquiv.symm ((finCongr (Nat.add_sub_of_le h)).symm j)) := rfl
  rw [e1]
  by_cases hi : (i : ℕ) < m <;> by_cases hj : (j : ℕ) < m
  · rw [finSumFinEquiv_symm_cast_of_lt _ i hi, finSumFinEquiv_symm_cast_of_lt _ j hj,
      dite_eq_left ⟨hi, hj⟩]
    rfl
  · rw [finSumFinEquiv_symm_cast_of_lt _ i hi,
      finSumFinEquiv_symm_cast_of_le _ j (not_lt.mp hj), dite_eq_right (fun h' => hj h'.2),
      Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, Matrix.one_apply_ne]
    intro hij
    exact hj (hij ▸ hi)
  · rw [finSumFinEquiv_symm_cast_of_le _ i (not_lt.mp hi),
      finSumFinEquiv_symm_cast_of_lt _ j hj, dite_eq_right (fun h' => hi h'.1),
      Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, Matrix.one_apply_ne]
    intro hij
    exact hi (hij ▸ hj)
  · rw [finSumFinEquiv_symm_cast_of_le _ i (not_lt.mp hi),
      finSumFinEquiv_symm_cast_of_le _ j (not_lt.mp hj), dite_eq_right (fun h' => hi h'.1),
      Matrix.fromBlocks_apply₂₂]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne]
      intro h'
      apply hij
      ext
      have := congrArg Fin.val h'
      simp only at this
      omega

/-- Rows of `diag(M, I)` with index at least the size of `M` are standard basis rows. -/
theorem padGL_row {m n : ℕ} (h : m ≤ n) (M : Matrix.GeneralLinearGroup (Fin m) R) (i : Fin n)
    (hi : m ≤ (i : ℕ)) (j : Fin n) :
    (padGL h M : Matrix (Fin n) (Fin n) R) i j = (1 : Matrix (Fin n) (Fin n) R) i j := by
  rw [padGL_apply, dite_eq_right (fun h' => absurd h'.1 (not_lt.mpr hi))]

/-- Columns of `diag(M, I)` with index at least the size of `M` are standard basis
columns. -/
theorem padGL_col {m n : ℕ} (h : m ≤ n) (M : Matrix.GeneralLinearGroup (Fin m) R) (j : Fin n)
    (hj : m ≤ (j : ℕ)) (i : Fin n) :
    (padGL h M : Matrix (Fin n) (Fin n) R) i j = (1 : Matrix (Fin n) (Fin n) R) i j := by
  rw [padGL_apply, dite_eq_right (fun h' => absurd h'.2 (not_lt.mpr hj))]

/-- Padding twice is padding once. -/
theorem padGL_padGL {m k n : ℕ} (h₁ : m ≤ k) (h₂ : k ≤ n)
    (M : Matrix.GeneralLinearGroup (Fin m) R) :
    padGL h₂ (padGL h₁ M) = padGL (h₁.trans h₂) M := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [padGL_apply, padGL_apply]
  by_cases hij : (i : ℕ) < m ∧ (j : ℕ) < m
  · rw [dite_eq_left ⟨hij.1.trans_le h₁, hij.2.trans_le h₁⟩, padGL_apply, dite_eq_left hij, dite_eq_left hij]
  · rw [dite_eq_right hij]
    by_cases hk : (i : ℕ) < k ∧ (j : ℕ) < k
    · rw [dite_eq_left hk, padGL_apply, dite_eq_right hij]
      by_cases he : i = j
      · subst he
        simp
      · rw [Matrix.one_apply_ne he, Matrix.one_apply_ne]
        intro h'
        exact he (Fin.ext (by simpa using congrArg Fin.val h'))
    · rw [dite_eq_right hk]

/-- Padding commutes with applying a ring homomorphism to the entries. -/
theorem padGL_map {S : Type*} [CommRing S] (f : R →+* S) {m n : ℕ} (h : m ≤ n)
    (M : Matrix.GeneralLinearGroup (Fin m) R) :
    padGL h (Matrix.GeneralLinearGroup.map f M) = Matrix.GeneralLinearGroup.map f (padGL h M) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [padGL_apply, Matrix.GeneralLinearGroup.map_apply, padGL_apply]
  split_ifs with hij
  · rfl
  · by_cases he : i = j
    · subst he
      simp
    · rw [Matrix.one_apply_ne he, Matrix.one_apply_ne he, map_zero]

/-- `det diag(M, I) = det M`. -/
theorem det_padGL {m n : ℕ} (h : m ≤ n) (M : Matrix.GeneralLinearGroup (Fin m) R) :
    (padGL h M : Matrix (Fin n) (Fin n) R).det = (M : Matrix (Fin m) (Fin m) R).det := by
  have e1 : (padGL h M : Matrix (Fin n) (Fin n) R) =
      Matrix.reindex (finCongr (Nat.add_sub_of_le h)) (finCongr (Nat.add_sub_of_le h))
        (Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (M : Matrix (Fin m) (Fin m) R) 0 0
            (1 : Matrix (Fin (n - m)) (Fin (n - m)) R))) := rfl
  rw [e1, Matrix.det_reindex_self, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one]

end Matrix

section Weight

variable {n k : ℕ}

theorem projectionWeight_nonpos (i : Fin n) : projectionWeight n k i ≤ 0 := by
  simp only [projectionWeight]
  omega

theorem projectionWeight_eq_zero {i : Fin n} (hi : (i : ℕ) ≤ k) : projectionWeight n k i = 0 := by
  simp only [projectionWeight]
  omega

theorem projectionWeight_antitone {i j : Fin n} (hij : i ≤ j) :
    projectionWeight n k j ≤ projectionWeight n k i := by
  have : (i : ℕ) ≤ j := hij
  simp only [projectionWeight]
  omega

theorem projectionWeight_lt {i j : Fin n} (hij : projectionWeight n k i < projectionWeight n k j) :
    k < (i : ℕ) := by
  simp only [projectionWeight] at hij
  omega

end Weight

section Radical

variable (A : Type*) [CommRing A] {n k : ℕ}

local notation "Y" => Langlands.GroupScheme.GeneralLinear.blockUnipotentSubgroup A
  (projectionWeight n k)

variable {A}

/-- The `k`-th column of an element of `Y_(n,k)` is the `k`-th standard basis column. -/
theorem radical_col {y : Matrix.GeneralLinearGroup (Fin n) A} (hy : y ∈ Y) (c : Fin n)
    (hc : (c : ℕ) = k) (i : Fin n) :
    (y : Matrix (Fin n) (Fin n) A) i c = (1 : Matrix (Fin n) (Fin n) A) i c :=
  hy i c (by rw [projectionWeight_eq_zero hc.le]; exact projectionWeight_nonpos i)

/-- The last row of an element of `Y_(n,k)` is the last standard basis row. -/
theorem radical_row {y : Matrix.GeneralLinearGroup (Fin (n + 1)) A}
    (hy : y ∈ Langlands.GroupScheme.GeneralLinear.blockUnipotentSubgroup A
      (projectionWeight (n + 1) k)) (j : Fin (n + 1)) :
    (y : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (Fin.last n) j =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (Fin.last n) j :=
  hy _ j (projectionWeight_antitone (Fin.le_last j))

/-- Elements of `Y_(n,k)` are upper triangular. -/
theorem radical_upper {y : Matrix.GeneralLinearGroup (Fin n) A} (hy : y ∈ Y) :
    (y : Matrix (Fin n) (Fin n) A).IsUpperTriangular := by
  intro i j hji
  rw [hy i j (projectionWeight_antitone hji.le)]
  exact Matrix.one_apply_ne (ne_of_gt hji)

/-- Elements of `Y_(n,k)` have determinant one. -/
theorem radical_det {y : Matrix.GeneralLinearGroup (Fin n) A} (hy : y ∈ Y) :
    (y : Matrix (Fin n) (Fin n) A).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (radical_upper hy)]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [hy i i le_rfl, Matrix.one_apply_eq]

/-- The superdiagonal entries of a product of upper unitriangular matrices add. -/
theorem superdiag_mul {N P : Matrix (Fin (n + 1)) (Fin (n + 1)) A} (hN : N.IsUpperTriangular)
    (hP : P.IsUpperTriangular) (hNd : ∀ i, N i i = 1) (hPd : ∀ i, P i i = 1) (i : Fin n) :
    (N * P) i.castSucc i.succ = N i.castSucc i.succ + P i.castSucc i.succ := by
  rw [Matrix.mul_apply, Finset.sum_eq_add i.castSucc i.succ (Fin.castSucc_lt_succ).ne]
  · rw [hNd, hPd, one_mul, mul_one, add_comm]
  · intro c _ hc
    rcases lt_or_gt_of_ne hc.1 with h1 | h1
    · rw [show N i.castSucc c = 0 from hN h1, zero_mul]
    · have h2 : i.succ < c := by
        rcases lt_or_gt_of_ne hc.2 with h3 | h3
        · exact absurd (Fin.castSucc_lt_iff_succ_le.mp h1) (not_le.mpr h3)
        · exact h3
      rw [show P c i.succ = 0 from hP h2, mul_zero]
  · simp
  · simp

/-- On `Y_(n,k)`, the superdiagonal entries of a product add. -/
theorem radical_superdiag_mul {y z : Matrix.GeneralLinearGroup (Fin (n + 1)) A}
    (hy : y ∈ Langlands.GroupScheme.GeneralLinear.blockUnipotentSubgroup A
      (projectionWeight (n + 1) k))
    (hz : z ∈ Langlands.GroupScheme.GeneralLinear.blockUnipotentSubgroup A
      (projectionWeight (n + 1) k)) (i : Fin n) :
    ((y * z : Matrix.GeneralLinearGroup (Fin (n + 1)) A) : Matrix _ _ A) i.castSucc i.succ =
      (y : Matrix _ _ A) i.castSucc i.succ + (z : Matrix _ _ A) i.castSucc i.succ := by
  rw [Units.val_mul]
  exact superdiag_mul (radical_upper hy) (radical_upper hz)
    (fun j => by rw [hy j j le_rfl, Matrix.one_apply_eq])
    (fun j => by rw [hz j j le_rfl, Matrix.one_apply_eq]) i

/-- **The radical is normalized by the block parabolic subgroup.** -/
theorem radical_conj {y P : Matrix.GeneralLinearGroup (Fin n) A} (hy : y ∈ Y)
    (hP : P ∈ Langlands.GroupScheme.GeneralLinear.blockParabolicSubgroup A
      (projectionWeight n k)) :
    P⁻¹ * y * P ∈ Y := by
  have hy' := (Langlands.GroupScheme.GeneralLinear.blockUnipotent_iff A _ _).1 hy
  have hPi := (Langlands.GroupScheme.GeneralLinear.blockParabolicSubgroup A
    (projectionWeight n k)).inv_mem hP
  refine (Langlands.GroupScheme.GeneralLinear.blockUnipotent_iff A _ _).2 ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul]
    exact (hPi.mul hy'.1).mul hP
  · rw [Units.val_mul, Units.val_mul,
      Langlands.GroupScheme.GeneralLinear.blockDiagonalPart_mul A _ (hPi.mul hy'.1) hP,
      Langlands.GroupScheme.GeneralLinear.blockDiagonalPart_mul A _ hPi hy'.1, hy'.2, mul_one,
      ← Langlands.GroupScheme.GeneralLinear.blockDiagonalPart_mul A _ hPi hP, ← Units.val_mul,
      inv_mul_cancel, Units.val_one,
      Langlands.GroupScheme.GeneralLinear.blockDiagonalPart_one]

/-- `diag(M, I)` lies in the block parabolic subgroup when `M` has size at most `k + 1`. -/
theorem padGL_mem_parabolic {m : ℕ} (h : m ≤ n) (hm : m ≤ k + 1)
    (M : Matrix.GeneralLinearGroup (Fin m) A) :
    padGL h M ∈ Langlands.GroupScheme.GeneralLinear.blockParabolicSubgroup A
      (projectionWeight n k) := by
  intro i j hij
  change projectionWeight n k i < projectionWeight n k j at hij
  have hi := projectionWeight_lt hij
  rw [padGL_row h M i (by omega), Matrix.one_apply_ne]
  rintro rfl
  exact lt_irrefl _ hij

/-- **Conjugation by `diag(M, I)` fixes the superdiagonal of `Y_(n,k)`** when `M` has size at
most `k`. -/
theorem radical_superdiag_conj {m : ℕ} (h : m ≤ n + 1) (hm : m ≤ k)
    (M : Matrix.GeneralLinearGroup (Fin m) A) {y : Matrix.GeneralLinearGroup (Fin (n + 1)) A}
    (hy : y ∈ Langlands.GroupScheme.GeneralLinear.blockUnipotentSubgroup A
      (projectionWeight (n + 1) k)) (i : Fin n) :
    (((padGL h M)⁻¹ * y * padGL h M : Matrix.GeneralLinearGroup (Fin (n + 1)) A) :
      Matrix _ _ A) i.castSucc i.succ = (y : Matrix _ _ A) i.castSucc i.succ := by
  by_cases hik : (i : ℕ) + 1 ≤ k
  · have hz := radical_conj hy (padGL_mem_parabolic h (by omega) M)
    have he : projectionWeight (n + 1) k i.castSucc ≤ projectionWeight (n + 1) k i.succ := by
      rw [projectionWeight_eq_zero (by simp; omega), projectionWeight_eq_zero (by simp; omega)]
    rw [hz _ _ he, hy _ _ he]
  · rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc,
      mul_apply_of_row (i := i.castSucc) _ ?_ i.succ,
      mul_apply_of_col (j := i.succ) _ ?_ i.castSucc]
    · intro c
      exact padGL_col h M i.succ (by simp; omega) c
    · intro c
      rw [← map_inv]
      exact padGL_row h M⁻¹ i.castSucc (by simp; omega) c

end Radical

end Langlands.Global.RankinSelbergGlobal.UnequalAnalytic
