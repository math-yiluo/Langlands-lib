import Langlands.Group.GL.UpperBruhatRankStatement
import Langlands.Group.GL.UpperBruhatProof

/-! Proof of the lower-left rank characterization of the actual upper Bruhat cells. -/

namespace Langlands.GeneralLinear

universe u

namespace UpperBruhatRank

variable {K : Type u} [Field K] {n : ℕ}

/-- The zero-padded lower-left corner of the statement: rows `r` with `i ≤ r` and
columns `c` with `c < j` are kept, every other entry is replaced by zero. -/
def corner (i j : Fin (n + 1)) (M : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  fun r c => if i.val ≤ r.val ∧ c.val < j.val then M r c else 0

/-- The diagonal `0/1` mask keeping the rows `r` with `i ≤ r`. -/
def rowMask (i : Fin (n + 1)) : Matrix (Fin n) (Fin n) K :=
  Matrix.diagonal fun r => if i.val ≤ r.val then 1 else 0

/-- The diagonal `0/1` mask keeping the columns `c` with `c < j`. -/
def colMask (j : Fin (n + 1)) : Matrix (Fin n) (Fin n) K :=
  Matrix.diagonal fun c => if c.val < j.val then 1 else 0

theorem corner_eq_mul (i j : Fin (n + 1)) (M : Matrix (Fin n) (Fin n) K) :
    corner i j M = rowMask i * M * colMask j := by
  ext r c
  simp only [corner, rowMask, colMask, Matrix.mul_diagonal, Matrix.diagonal_mul]
  split_ifs <;> simp_all

/-- Row mask absorption: an upper triangular matrix maps no kept row into a dropped one. -/
theorem rowMask_mul_triangular (i : Fin (n + 1)) {b : Matrix (Fin n) (Fin n) K}
    (hb : ∀ r s : Fin n, s < r → b r s = 0) :
    rowMask i * b = rowMask i * b * rowMask i := by
  ext r s
  simp only [rowMask, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hr : i.val ≤ r.val
  · by_cases hs : i.val ≤ s.val
    · simp [hs]
    · have hsr : s < r := by
        rw [Fin.lt_def]
        omega
      simp [hs, hb r s hsr]
  · simp [hr]

/-- Column mask absorption: an upper triangular matrix maps no kept column outside the kept
columns. -/
theorem triangular_mul_colMask (j : Fin (n + 1)) {b : Matrix (Fin n) (Fin n) K}
    (hb : ∀ r s : Fin n, s < r → b r s = 0) :
    b * colMask j = colMask j * b * colMask j := by
  ext s c
  simp only [colMask, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hc : c.val < j.val
  · by_cases hs : s.val < j.val
    · simp [hs]
    · have hcs : c < s := by
        rw [Fin.lt_def]
        omega
      simp [hs, hb s c hcs]
  · simp [hc]

theorem rank_corner_triangular_mul_le (i j : Fin (n + 1)) {b : Matrix (Fin n) (Fin n) K}
    (hb : ∀ r s : Fin n, s < r → b r s = 0) (M : Matrix (Fin n) (Fin n) K) :
    (corner i j (b * M)).rank ≤ (corner i j M).rank := by
  have key := rowMask_mul_triangular i hb
  have h : corner i j (b * M) = (rowMask i * b) * corner i j M :=
    calc corner i j (b * M) = rowMask i * b * (M * colMask j) := by
          rw [corner_eq_mul]
          simp only [Matrix.mul_assoc]
      _ = rowMask i * b * rowMask i * (M * colMask j) := by
          conv_lhs => rw [key]
      _ = (rowMask i * b) * corner i j M := by
          rw [corner_eq_mul]
          simp only [Matrix.mul_assoc]
  rw [h]
  exact Matrix.rank_mul_le_right _ _

theorem rank_corner_mul_triangular_le (i j : Fin (n + 1)) {b : Matrix (Fin n) (Fin n) K}
    (hb : ∀ r s : Fin n, s < r → b r s = 0) (M : Matrix (Fin n) (Fin n) K) :
    (corner i j (M * b)).rank ≤ (corner i j M).rank := by
  have key := triangular_mul_colMask j hb
  have h : corner i j (M * b) = corner i j M * (b * colMask j) :=
    calc corner i j (M * b) = rowMask i * M * (b * colMask j) := by
          rw [corner_eq_mul]
          simp only [Matrix.mul_assoc]
      _ = rowMask i * M * (colMask j * b * colMask j) := by
          rw [key]
      _ = corner i j M * (b * colMask j) := by
          rw [corner_eq_mul]
          simp only [Matrix.mul_assoc]
  rw [h]
  exact Matrix.rank_mul_le_left _ _

/-- Left multiplication by the upper triangular subgroup preserves every corner rank. -/
theorem rank_corner_triangular_mul (i j : Fin (n + 1)) {b : GeneralLinear n K}
    (hb : b ∈ upperTriangularSubgroup n K) (M : Matrix (Fin n) (Fin n) K) :
    (corner i j ((b : Matrix (Fin n) (Fin n) K) * M)).rank = (corner i j M).rank := by
  apply le_antisymm
    (rank_corner_triangular_mul_le i j ((mem_upperTriangularSubgroup_iff b).mp hb) M)
  have hinv := (mem_upperTriangularSubgroup_iff b⁻¹).mp (inv_mem hb)
  have h := rank_corner_triangular_mul_le i j hinv ((b : Matrix (Fin n) (Fin n) K) * M)
  rwa [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul] at h

/-- Right multiplication by the upper triangular subgroup preserves every corner rank. -/
theorem rank_corner_mul_triangular (i j : Fin (n + 1)) {b : GeneralLinear n K}
    (hb : b ∈ upperTriangularSubgroup n K) (M : Matrix (Fin n) (Fin n) K) :
    (corner i j (M * (b : Matrix (Fin n) (Fin n) K))).rank = (corner i j M).rank := by
  apply le_antisymm
    (rank_corner_mul_triangular_le i j ((mem_upperTriangularSubgroup_iff b).mp hb) M)
  have hinv := (mem_upperTriangularSubgroup_iff b⁻¹).mp (inv_mem hb)
  have h := rank_corner_mul_triangular_le i j hinv (M * (b : Matrix (Fin n) (Fin n) K))
  rwa [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.mul_one] at h

/-- Every corner rank is constant on each double coset `B * p * B`. -/
theorem rank_corner_triangular_mul_mul (i j : Fin (n + 1)) {b₁ b₂ : GeneralLinear n K}
    (hb₁ : b₁ ∈ upperTriangularSubgroup n K) (hb₂ : b₂ ∈ upperTriangularSubgroup n K)
    (p : GeneralLinear n K) :
    (corner i j ((b₁ * p * b₂ : GeneralLinear n K) : Matrix (Fin n) (Fin n) K)).rank =
      (corner i j (p : Matrix (Fin n) (Fin n) K)).rank := by
  rw [Units.val_mul, Units.val_mul, rank_corner_mul_triangular i j hb₂,
    rank_corner_triangular_mul i j hb₁]

/-- Left multiplication by an invertible matrix preserves rank. -/
theorem rank_units_mul (A : GeneralLinear n K) (M : Matrix (Fin n) (Fin n) K) :
    ((A : Matrix (Fin n) (Fin n) K) * M).rank = M.rank := by
  apply le_antisymm (Matrix.rank_mul_le_right _ _)
  calc M.rank
        = ((↑A⁻¹ : Matrix (Fin n) (Fin n) K) * ((A : Matrix (Fin n) (Fin n) K) * M)).rank := by
        rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    _ ≤ ((A : Matrix (Fin n) (Fin n) K) * M).rank := Matrix.rank_mul_le_right _ _

/-- The number of columns `c < k` whose image under `w` lies in a row `r ≥ i`. -/
def count (w : Equiv.Perm (Fin n)) (i : Fin (n + 1)) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun c : Fin n => c.val < k ∧ i.val ≤ (w c).val).card

/-- A permutation corner is the permutation matrix times a diagonal `0/1` matrix. -/
theorem corner_permutation (i j : Fin (n + 1)) (w : Equiv.Perm (Fin n)) :
    corner i j (permutation n K w : Matrix (Fin n) (Fin n) K) =
      (permutation n K w : Matrix (Fin n) (Fin n) K) *
        Matrix.diagonal fun c => if c.val < j.val ∧ i.val ≤ (w c).val then 1 else 0 := by
  have hp : ∀ r c : Fin n,
      (permutation n K w : Matrix (Fin n) (Fin n) K) r c = if w c = r then 1 else 0 :=
    permutation_entry n K w
  ext r c
  simp only [corner, Matrix.mul_diagonal, hp]
  by_cases hrc : w c = r
  · subst hrc
    by_cases h1 : i.val ≤ (w c).val <;> by_cases h2 : c.val < j.val <;> simp [h1, h2]
  · simp [hrc]

/-- The rank of a permutation corner is the corresponding column count. -/
theorem rank_corner_permutation (i j : Fin (n + 1)) (w : Equiv.Perm (Fin n)) :
    (corner i j (permutation n K w : Matrix (Fin n) (Fin n) K)).rank = count w i j.val := by
  classical
  rw [corner_permutation, rank_units_mul, Matrix.rank_diagonal, Fintype.card_subtype, count]
  congr 1
  apply Finset.filter_congr
  intro c _
  by_cases h : c.val < j.val ∧ i.val ≤ (w c).val <;> simp [h]

/-- Adding the column `c` to the column range adds one exactly when `i ≤ w c`. -/
theorem count_succ (w : Equiv.Perm (Fin n)) (i : Fin (n + 1)) (c : Fin n) :
    count w i (c.val + 1) = count w i c.val + if i.val ≤ (w c).val then 1 else 0 := by
  unfold count
  by_cases hc : i.val ≤ (w c).val
  · simp only [hc, ↓reduceIte]
    have hset : (Finset.univ.filter fun d : Fin n => d.val < c.val + 1 ∧ i.val ≤ (w d).val) =
        insert c (Finset.univ.filter fun d : Fin n => d.val < c.val ∧ i.val ≤ (w d).val) := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨hd, hw⟩
        by_cases hdc : d = c
        · exact Or.inl hdc
        · have hne : d.val ≠ c.val := fun h => hdc (Fin.ext h)
          exact Or.inr ⟨by omega, hw⟩
      · rintro (rfl | ⟨hd, hw⟩)
        · exact ⟨by omega, hc⟩
        · exact ⟨by omega, hw⟩
    rw [hset, Finset.card_insert_of_notMem]
    simp
  · simp only [hc, ↓reduceIte, add_zero]
    congr 1
    apply Finset.filter_congr
    intro d _
    constructor
    · rintro ⟨hd, hw⟩
      have hne : d ≠ c := by
        rintro rfl
        exact hc hw
      have hne' : d.val ≠ c.val := fun h => hne (Fin.ext h)
      exact ⟨by omega, hw⟩
    · rintro ⟨hd, hw⟩
      exact ⟨by omega, hw⟩

/-- The column-count profile of a permutation determines the permutation. -/
theorem perm_eq_of_count_eq {v w : Equiv.Perm (Fin n)}
    (h : ∀ i j : Fin (n + 1), count v i j.val = count w i j.val) : v = w := by
  have hstep : ∀ (i : Fin (n + 1)) (c : Fin n), i.val ≤ (v c).val ↔ i.val ≤ (w c).val := by
    intro i c
    have h1 := h i c.succ
    have h0 := h i c.castSucc
    simp only [Fin.val_succ, Fin.val_castSucc] at h1 h0
    rw [count_succ, count_succ, h0] at h1
    by_cases hv : i.val ≤ (v c).val <;> by_cases hw : i.val ≤ (w c).val <;>
      simp [hv, hw] at h1 <;> simp [hv, hw]
  refine Equiv.ext fun c => Fin.ext ?_
  have h₁ := (hstep ⟨(w c).val, by omega⟩ c).mpr le_rfl
  have h₂ := (hstep ⟨(v c).val, by omega⟩ c).mp le_rfl
  simp only at h₁ h₂
  omega

end UpperBruhatRank

open UpperBruhatRank in
/-- Lower-left corner ranks characterize every actual upper Bruhat cell over every field. -/
theorem upperBruhatRankCharacterization : UpperBruhatRankCharacterizationStatement.{u} := by
  intro K _ n w g
  change g ∈ upperBruhatCell n K w ↔
    ∀ i j : Fin (n + 1),
      (corner i j (g : Matrix (Fin n) (Fin n) K)).rank =
        (corner i j (permutation n K w : Matrix (Fin n) (Fin n) K)).rank
  constructor
  · rintro ⟨b₁, hb₁, b₂, hb₂, rfl⟩ i j
    exact rank_corner_triangular_mul_mul i j hb₁ hb₂ _
  · intro h
    obtain ⟨a, b, v, ha, hb, rfl⟩ := fieldUpperBruhatFactorizationTheorem K n g
    have ha' : a ∈ upperTriangularSubgroup n K := (mem_upperTriangularSubgroup_iff a).mpr ha
    have hb' : b ∈ upperTriangularSubgroup n K := (mem_upperTriangularSubgroup_iff b).mpr hb
    have hv : v = w := by
      apply perm_eq_of_count_eq
      intro i j
      rw [← rank_corner_permutation (K := K), ← rank_corner_permutation (K := K), ← h i j,
        rank_corner_triangular_mul_mul i j ha' hb']
    subst hv
    exact ⟨a, ha', b, hb', rfl⟩

end Langlands.GeneralLinear
