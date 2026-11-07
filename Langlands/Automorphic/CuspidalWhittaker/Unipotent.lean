import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Column and block unipotent matrices

Over a commutative ring, for square-zero `N` the matrix `1 + N` is invertible with inverse
`1 - N`. Two families are used for the unipotent integrals: the column matrices supported in
rows `< c` of column `c`, and the block matrices supported in rows `< m` and columns
`m ≤ j ≤ c`. We record their products, their conjugation by block matrices, and the mirabolic
and block subgroups that fix them.
-/

noncomputable section

namespace Langlands.Automorphic.CuspidalWhittaker

open Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

/-! ### Square-zero units -/

/-- `1 + N` for a square-zero matrix `N`, with inverse `1 - N`. -/
def sqZeroUnit (N : Matrix (Fin n) (Fin n) R) (h : N * N = 0) : GL (Fin n) R where
  val := 1 + N
  inv := 1 - N
  val_inv := by rw [add_mul, one_mul, mul_sub, mul_one, h, sub_zero, sub_add_cancel]
  inv_val := by rw [sub_mul, one_mul, mul_add, mul_one, h, add_zero, add_sub_cancel_right]

@[simp] theorem sqZeroUnit_val (N : Matrix (Fin n) (Fin n) R) (h : N * N = 0) :
    (sqZeroUnit N h : Matrix (Fin n) (Fin n) R) = 1 + N := rfl

@[simp] theorem sqZeroUnit_inv_val (N : Matrix (Fin n) (Fin n) R) (h : N * N = 0) :
    ((sqZeroUnit N h)⁻¹ : GL (Fin n) R).val = 1 - N := rfl

theorem sqZeroUnit_mul_eq {N M L : Matrix (Fin n) (Fin n) R} (hN : N * N = 0) (hM : M * M = 0)
    (hL : L * L = 0) (hNM : N * M = 0) (hsum : N + M = L) :
    sqZeroUnit N hN * sqZeroUnit M hM = sqZeroUnit L hL := by
  apply Units.ext
  simp only [Units.val_mul, sqZeroUnit_val]
  rw [← hsum, add_mul, one_mul, mul_add, mul_one, hNM, add_zero]
  abel

/-! ### Column matrices -/

/-- The matrix with entry `v i` at `(i, c)` for `i < c`, and zero elsewhere. -/
def colMat (c : Fin n) (v : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if (i : ℕ) < c ∧ (j : ℕ) = c then v i else 0

@[simp] theorem colMat_apply (c : Fin n) (v : Fin n → R) (i j : Fin n) :
    colMat c v i j = if (i : ℕ) < c ∧ (j : ℕ) = c then v i else 0 := rfl

theorem colMat_add (c : Fin n) (v w : Fin n → R) :
    colMat c (v + w) = colMat c v + colMat c w := by
  ext i j
  simp only [colMat_apply, Pi.add_apply, Matrix.add_apply]
  split_ifs <;> simp

theorem colMat_neg (c : Fin n) (v : Fin n → R) : colMat c (-v) = -colMat c v := by
  ext i j
  simp only [colMat_apply, Pi.neg_apply, Matrix.neg_apply]
  split_ifs <;> simp

@[simp] theorem colMat_zero (c : Fin n) : colMat c (0 : Fin n → R) = 0 := by
  ext i j
  simp

theorem colMat_congr (c : Fin n) {v w : Fin n → R} (h : ∀ i : Fin n, (i : ℕ) < c → v i = w i) :
    colMat c v = colMat c w := by
  ext i j
  simp only [colMat_apply]
  split_ifs with hij
  · exact h i hij.1
  · rfl

theorem colMat_mul_apply (c : Fin n) (v : Fin n → R) (M : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) : (colMat c v * M) i j = if (i : ℕ) < c then v i * M c j else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single c]
  · simp only [colMat_apply, and_true]
    split_ifs <;> simp
  · intro k _ hk
    have : (k : ℕ) ≠ c := fun h => hk (Fin.ext h)
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ c) h

theorem mul_colMat_apply (c : Fin n) (v : Fin n → R) (M : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) : (M * colMat c v) i j =
      if (j : ℕ) = c then ∑ k : Fin n, (if (k : ℕ) < c then M i k * v k else 0) else 0 := by
  rw [Matrix.mul_apply]
  split_ifs with hj
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [colMat_apply, hj, and_true, mul_ite, mul_zero]
  · refine Finset.sum_eq_zero fun k _ => ?_
    simp [hj]

theorem colMat_mul_eq_zero (c : Fin n) (v : Fin n → R) {M : Matrix (Fin n) (Fin n) R}
    (hM : ∀ j, M c j = 0) : colMat c v * M = 0 := by
  ext i j
  rw [colMat_mul_apply, hM]
  simp

theorem colMat_mul_colMat (c : Fin n) (v w : Fin n → R) : colMat c v * colMat c w = 0 :=
  colMat_mul_eq_zero c v fun j => by simp

/-- A matrix vanishing outside the rows and columns `< c` acts on column matrices through its
action on vectors. -/
theorem mul_colMat_of (c : Fin n) (v : Fin n → R) {M : Matrix (Fin n) (Fin n) R}
    (hM : ∀ i k : Fin n, ((c : ℕ) ≤ i ∨ (c : ℕ) ≤ k) → M i k = 0) :
    M * colMat c v = colMat c (M *ᵥ v) := by
  ext i j
  rw [mul_colMat_apply, colMat_apply]
  by_cases hj : (j : ℕ) = c
  · have hsum : ∑ k : Fin n, (if (k : ℕ) < c then M i k * v k else 0) = (M *ᵥ v) i := by
      rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs with hk
      · rfl
      · rw [hM i k (Or.inr (not_lt.mp hk)), zero_mul]
    rw [ite_eq_left hj, hsum]
    by_cases hi : (i : ℕ) < c
    · rw [ite_eq_left ⟨hi, hj⟩]
    · rw [ite_eq_right (fun h => hi h.1), Matrix.mulVec, dotProduct]
      exact Finset.sum_eq_zero fun k _ => by rw [hM i k (Or.inl (not_lt.mp hi)), zero_mul]
  · rw [ite_eq_right hj, ite_eq_right (fun h => hj h.2)]

/-- The column unipotent element `1 + colMat c v`. -/
def colUnit (c : Fin n) (v : Fin n → R) : GL (Fin n) R :=
  sqZeroUnit (colMat c v) (colMat_mul_colMat c v v)

@[simp] theorem colUnit_val (c : Fin n) (v : Fin n → R) :
    (colUnit c v : Matrix (Fin n) (Fin n) R) = 1 + colMat c v := rfl

theorem colUnit_mul (c : Fin n) (v w : Fin n → R) :
    colUnit c v * colUnit c w = colUnit c (v + w) :=
  sqZeroUnit_mul_eq _ _ _ (colMat_mul_colMat c v w) (colMat_add c v w).symm

@[simp] theorem colUnit_zero (c : Fin n) : colUnit c (0 : Fin n → R) = 1 := by
  apply Units.ext
  simp

theorem colUnit_congr (c : Fin n) {v w : Fin n → R} (h : ∀ i : Fin n, (i : ℕ) < c → v i = w i) :
    colUnit c v = colUnit c w :=
  Units.ext (by simp [colMat_congr c h])

theorem colUnit_comm (c : Fin n) (v w : Fin n → R) :
    colUnit c v * colUnit c w = colUnit c w * colUnit c v := by
  rw [colUnit_mul, colUnit_mul, add_comm]

/-! ### Block matrices -/

/-- The matrix with entry `X (i, j)` at `(i, j)` for `i < m ≤ j ≤ c`, and zero elsewhere. -/
def blkMat (m c : ℕ) (X : Fin n × Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if (i : ℕ) < m ∧ m ≤ (j : ℕ) ∧ (j : ℕ) ≤ c then X (i, j) else 0

@[simp] theorem blkMat_apply (m c : ℕ) (X : Fin n × Fin n → R) (i j : Fin n) :
    blkMat m c X i j = if (i : ℕ) < m ∧ m ≤ (j : ℕ) ∧ (j : ℕ) ≤ c then X (i, j) else 0 := rfl

theorem blkMat_add (m c : ℕ) (X Y : Fin n × Fin n → R) :
    blkMat m c (X + Y) = blkMat m c X + blkMat m c Y := by
  ext i j
  simp only [blkMat_apply, Pi.add_apply, Matrix.add_apply]
  split_ifs <;> simp

theorem blkMat_row_eq_zero (m c : ℕ) (X : Fin n × Fin n → R) {i : Fin n} (hi : m ≤ (i : ℕ))
    (j : Fin n) : blkMat m c X i j = 0 := by
  rw [blkMat_apply, ite_eq_right (fun h => by omega)]

theorem blkMat_mul_blkMat (m c c' : ℕ) (X Y : Fin n × Fin n → R) :
    blkMat m c X * blkMat m c' Y = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : m ≤ (k : ℕ)
  · rw [blkMat_row_eq_zero m c' Y hk, mul_zero]
  · rw [blkMat_apply, ite_eq_right (fun h => hk h.2.1), zero_mul]

/-- The block unipotent element `1 + blkMat m c X`. -/
def blkUnit (m c : ℕ) (X : Fin n × Fin n → R) : GL (Fin n) R :=
  sqZeroUnit (blkMat m c X) (blkMat_mul_blkMat m c c X X)

@[simp] theorem blkUnit_val (m c : ℕ) (X : Fin n × Fin n → R) :
    (blkUnit m c X : Matrix (Fin n) (Fin n) R) = 1 + blkMat m c X := rfl

theorem blkUnit_mul (m c : ℕ) (X Y : Fin n × Fin n → R) :
    blkUnit m c X * blkUnit m c Y = blkUnit m c (X + Y) :=
  sqZeroUnit_mul_eq _ _ _ (blkMat_mul_blkMat m c c X Y) (blkMat_add m c X Y).symm

theorem colMat_mul_blkMat (c : Fin n) (v : Fin n → R) {m : ℕ} (hm : m ≤ (c : ℕ)) (c' : ℕ)
    (X : Fin n × Fin n → R) : colMat c v * blkMat m c' X = 0 :=
  colMat_mul_eq_zero c v fun j => blkMat_row_eq_zero m c' X hm j

theorem blkMat_mul_colMat (c : Fin n) (v : Fin n → R) {m c' : ℕ} (hm : m ≤ (c : ℕ))
    (hc : c' < (c : ℕ)) (X : Fin n × Fin n → R) :
    blkMat m c' X * colMat c v = colMat c (blkMat m c' X *ᵥ v) := by
  refine mul_colMat_of c v fun i k hik => ?_
  rw [blkMat_apply, ite_eq_right (fun h => by omega)]

/-- Replace column `c` of a matrix of coordinates by `v`. -/
def updateCol (X : Fin n × Fin n → R) (c : Fin n) (v : Fin n → R) : Fin n × Fin n → R :=
  fun p => if p.2 = c then v p.1 else X p

/-- Truncation of a vector to its coordinates `< m`. -/
def truncVec (m : ℕ) (v : Fin n → R) : Fin n → R := fun i => if (i : ℕ) < m then v i else 0

theorem truncVec_add (m : ℕ) (v w : Fin n → R) :
    truncVec m (v + w) = truncVec m v + truncVec m w := by
  funext i
  simp only [truncVec, Pi.add_apply]
  split_ifs <;> simp

theorem blkMat_updateCol (c : Fin n) {m c' : ℕ} (hc : (c : ℕ) = c' + 1) (hm : m ≤ c')
    (X : Fin n × Fin n → R) (v : Fin n → R) :
    blkMat m (c : ℕ) (updateCol X c v) = blkMat m c' X + colMat c (truncVec m v) := by
  ext i j
  simp only [blkMat_apply, colMat_apply, Matrix.add_apply, updateCol, truncVec]
  by_cases hj : j = c
  · subst hj
    have hjm : m ≤ (j : ℕ) := by omega
    have hjc : ¬((j : ℕ) ≤ c') := by omega
    by_cases hi : (i : ℕ) < m
    · have hij : (i : ℕ) < j := by omega
      simp [hi, hjm, hjc, hij]
    · simp [hi, hjc]
  · have hj' : (j : ℕ) ≠ c := fun h => hj (Fin.ext h)
    simp only [hj, ite_false]
    have hcol : ¬((i : ℕ) < c ∧ (j : ℕ) = c) := fun h => hj' h.2
    rw [ite_eq_right hcol, add_zero]
    by_cases h1 : (i : ℕ) < m ∧ m ≤ (j : ℕ) ∧ (j : ℕ) ≤ c'
    · rw [ite_eq_left ⟨h1.1, h1.2.1, by omega⟩, ite_eq_left h1]
    · rw [ite_eq_right h1, ite_eq_right (fun h => h1 ⟨h.1, h.2.1, by omega⟩)]

/-! ### Splitting identities for the block integrals -/

theorem updateCol_add (X Y : Fin n × Fin n → R) (c : Fin n) (v w : Fin n → R) :
    updateCol (X + Y) c (v + w) = updateCol X c v + updateCol Y c w := by
  funext p
  simp only [updateCol, Pi.add_apply]
  split_ifs <;> rfl

theorem updateCol_self_add (X : Fin n × Fin n → R) (c : Fin n) (z : Fin n → R) :
    updateCol X c (z + fun i => X (i, c)) = X + updateCol 0 c z := by
  funext p
  simp only [updateCol, Pi.add_apply, Pi.zero_apply]
  split_ifs with h
  · rw [← h, add_comm]
  · rw [add_zero]

theorem truncVec_blkMat_mulVec (m c : ℕ) (X : Fin n × Fin n → R) (w : Fin n → R) :
    truncVec m (blkMat m c X *ᵥ w) = blkMat m c X *ᵥ w := by
  funext i
  simp only [truncVec]
  split_ifs with hi
  · rfl
  · rw [Matrix.mulVec, dotProduct]
    exact (Finset.sum_eq_zero fun j _ => by
      rw [blkMat_row_eq_zero m c X (not_lt.mp hi), zero_mul]).symm

theorem truncVec_truncVec (m : ℕ) (v : Fin n → R) : truncVec m (truncVec m v) = truncVec m v := by
  funext i
  simp only [truncVec]
  split_ifs <;> rfl

theorem truncVec_sub (m : ℕ) (v w : Fin n → R) :
    truncVec m (v - w) = truncVec m v - truncVec m w := by
  funext i
  simp only [truncVec, Pi.sub_apply]
  split_ifs <;> simp

/-- A column element supported in rows `< m` joins the block `i < m ≤ j ≤ c` as column `c+1`. -/
theorem colUnit_truncVec_mul_blkUnit (col : Fin n) {m c : ℕ} (hm : m ≤ c)
    (hcol : (col : ℕ) = c + 1) (X : Fin n × Fin n → R) (z : Fin n → R) :
    colUnit col (truncVec m z) * blkUnit m c X = blkUnit m (c + 1) (updateCol X col z) := by
  refine sqZeroUnit_mul_eq _ _ _ (colMat_mul_blkMat col _ (by omega) c X) ?_
  rw [← hcol, blkMat_updateCol col hcol hm, add_comm]

/-- Splitting a column element against a block element. -/
theorem colUnit_mul_blkUnit_split (col : Fin n) {m c : ℕ} (hm : m ≤ c)
    (hcol : (col : ℕ) = c + 1) (X : Fin n × Fin n → R) (y : Fin n → R) :
    colUnit col y * blkUnit m c X =
      colUnit col (truncVec m y - blkMat m c X *ᵥ (y - truncVec m y)) * blkUnit m c X *
        colUnit col (y - truncVec m y) := by
  apply Units.ext
  simp only [Units.val_mul, colUnit_val, blkUnit_val]
  set N := blkMat m c X with hN
  set a := truncVec m y - N *ᵥ (y - truncVec m y) with ha
  set b := y - truncVec m y with hb
  have hCN : colMat col y * N = 0 := colMat_mul_blkMat col y (by omega) c X
  have hAN : colMat col a * N = 0 := colMat_mul_blkMat col a (by omega) c X
  have hAB : colMat col a * colMat col b = 0 := colMat_mul_colMat col a b
  have hNB : N * colMat col b = colMat col (N *ᵥ b) :=
    blkMat_mul_colMat col b (by omega) (by omega) X
  have hsum : colMat col y = colMat col a + colMat col b + colMat col (N *ᵥ b) := by
    rw [← colMat_add, ← colMat_add, ha, hb]
    congr 1
    abel
  simp only [add_mul, mul_add, one_mul, mul_one, hCN, hAN, hAB, hNB, zero_mul, add_zero]
  rw [hsum]
  abel

/-- Moving a column element across a block element of width `c + 1`. -/
theorem blkUnit_updateCol_mul_colUnit (col : Fin n) {m c : ℕ} (hm : m ≤ c)
    (hcol : (col : ℕ) = c + 1) (X : Fin n × Fin n → R) (z w : Fin n → R) :
    blkUnit m (c + 1) (updateCol X col z) * colUnit col w =
      colUnit col w * blkUnit m (c + 1) (updateCol X col (z + blkMat m c X *ᵥ w)) := by
  apply Units.ext
  simp only [Units.val_mul, colUnit_val, blkUnit_val]
  rw [← hcol, blkMat_updateCol col hcol hm, blkMat_updateCol col hcol hm, truncVec_add,
    truncVec_blkMat_mulVec]
  have h1 : (blkMat m c X + colMat col (truncVec m z)) * colMat col w =
      colMat col (blkMat m c X *ᵥ w) := by
    rw [add_mul, blkMat_mul_colMat col w (by omega) (by omega) X, colMat_mul_colMat, add_zero]
  have h2 : colMat col w * (blkMat m c X + colMat col (truncVec m z + blkMat m c X *ᵥ w)) = 0 := by
    rw [mul_add, colMat_mul_blkMat col w (by omega) c X, colMat_mul_colMat, add_zero]
  rw [add_mul, one_mul, mul_add, mul_one, h1, mul_add, mul_one, add_mul, one_mul, h2, add_zero,
    colMat_add]
  abel

/-! ### Mirabolic and block conditions -/

/-- Matrices that are the identity in the rows `≥ c` and in the columns `> c`. -/
def IsMir (c : ℕ) (M : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j : Fin n, (c ≤ (i : ℕ) ∨ c < (j : ℕ)) → M i j = (1 : Matrix (Fin n) (Fin n) R) i j

/-- Matrices that are the identity in the rows `≥ c` and in the columns `≥ c`. -/
def IsBlk (c : ℕ) (M : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j : Fin n, (c ≤ (i : ℕ) ∨ c ≤ (j : ℕ)) → M i j = (1 : Matrix (Fin n) (Fin n) R) i j

theorem IsBlk.isMir {c : ℕ} {M : Matrix (Fin n) (Fin n) R} (h : IsBlk c M) : IsMir c M :=
  fun i j hij => h i j (hij.imp id le_of_lt)

theorem IsMir.isBlk_succ {c : ℕ} {M : Matrix (Fin n) (Fin n) R} (h : IsMir c M) :
    IsBlk (c + 1) M :=
  fun i j hij => h i j (hij.imp (fun h => by omega) (fun h => by omega))

theorem isMir_one (c : ℕ) : IsMir c (1 : Matrix (Fin n) (Fin n) R) := fun _ _ _ => rfl

theorem IsMir.mul {c : ℕ} {M N : Matrix (Fin n) (Fin n) R} (hM : IsMir c M) (hN : IsMir c N) :
    IsMir c (M * N) := by
  intro i j hij
  rcases hij with hi | hj
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hM i i (Or.inl hi), hN i j (Or.inl hi), Matrix.one_apply_eq, one_mul]
    · intro k _ hk
      rw [hM i k (Or.inl hi), Matrix.one_apply_ne (Ne.symm hk), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hM i j (Or.inr hj), hN j j (Or.inr hj), Matrix.one_apply_eq, mul_one]
    · intro k _ hk
      rw [hN k j (Or.inr hj), Matrix.one_apply_ne hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h

/-- The inverse of an invertible matrix in the mirabolic form keeps that form. -/
theorem IsMir.inv {c : ℕ} {g : GL (Fin n) R} (h : IsMir c g.val) : IsMir c (g⁻¹).val := by
  intro i j hij
  rcases hij with hi | hj
  · have e : (g.val * (g⁻¹).val) i j = (1 : Matrix (Fin n) (Fin n) R) i j := by
      rw [Units.mul_inv]
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at e
    · rwa [h i i (Or.inl hi), Matrix.one_apply_eq, one_mul] at e
    · intro k _ hk
      rw [h i k (Or.inl hi), Matrix.one_apply_ne (Ne.symm hk), zero_mul]
    · intro hh
      exact absurd (Finset.mem_univ i) hh
  · have e : ((g⁻¹).val * g.val) i j = (1 : Matrix (Fin n) (Fin n) R) i j := by
      rw [Units.inv_mul]
    rw [Matrix.mul_apply, Finset.sum_eq_single j] at e
    · rwa [h j j (Or.inr hj), Matrix.one_apply_eq, mul_one] at e
    · intro k _ hk
      rw [h k j (Or.inr hj), Matrix.one_apply_ne hk, mul_zero]
    · intro hh
      exact absurd (Finset.mem_univ j) hh

/-- The inverse of an invertible matrix in block form keeps that form. -/
theorem IsBlk.inv {c : ℕ} {g : GL (Fin n) R} (h : IsBlk c g.val) : IsBlk c (g⁻¹).val := by
  intro i j hij
  rcases hij with hi | hj
  · have e : (g.val * (g⁻¹).val) i j = (1 : Matrix (Fin n) (Fin n) R) i j := by
      rw [Units.mul_inv]
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at e
    · rwa [h i i (Or.inl hi), Matrix.one_apply_eq, one_mul] at e
    · intro k _ hk
      rw [h i k (Or.inl hi), Matrix.one_apply_ne (Ne.symm hk), zero_mul]
    · intro hh
      exact absurd (Finset.mem_univ i) hh
  · have e : ((g⁻¹).val * g.val) i j = (1 : Matrix (Fin n) (Fin n) R) i j := by
      rw [Units.inv_mul]
    rw [Matrix.mul_apply, Finset.sum_eq_single j] at e
    · rwa [h j j (Or.inr hj), Matrix.one_apply_eq, mul_one] at e
    · intro k _ hk
      rw [h k j (Or.inr hj), Matrix.one_apply_ne hk, mul_zero]
    · intro hh
      exact absurd (Finset.mem_univ j) hh

theorem isMir_colUnit (c : Fin n) (v : Fin n → R) : IsMir (c : ℕ) (colUnit c v).val := by
  intro i j hij
  rw [colUnit_val, Matrix.add_apply, colMat_apply, ite_eq_right (fun h => by omega), add_zero]

theorem isMir_blkUnit {m c c'' : ℕ} (hm : m ≤ c'') (hc : c ≤ c'') (X : Fin n × Fin n → R) :
    IsMir c'' (blkUnit m c X).val := by
  intro i j hij
  rw [blkUnit_val, Matrix.add_apply, blkMat_apply, ite_eq_right (fun h => by omega), add_zero]

theorem isBlk_blkUnit {m c c'' : ℕ} (hm : m ≤ c'') (hc : c < c'') (X : Fin n × Fin n → R) :
    IsBlk c'' (blkUnit m c X).val := by
  intro i j hij
  rw [blkUnit_val, Matrix.add_apply, blkMat_apply, ite_eq_right (fun h => by omega), add_zero]

/-- **Conjugation of a column element** by a block matrix. -/
theorem colUnit_mul_of_isBlk (c : Fin n) (v : Fin n → R) {g : GL (Fin n) R}
    (hg : IsBlk (c : ℕ) g.val) :
    colUnit c v * g = g * colUnit c ((g⁻¹ : GL (Fin n) R).val *ᵥ v) := by
  set G : Matrix (Fin n) (Fin n) R := g.val with hG
  set w : Fin n → R := (g⁻¹ : GL (Fin n) R).val *ᵥ v with hw
  have hGw : G *ᵥ w = v := by
    rw [hw, hG, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  apply Units.ext
  show (1 + colMat c v) * G = G * (1 + colMat c w)
  rw [add_mul, mul_add, one_mul, mul_one]
  congr 1
  ext i j
  rw [colMat_mul_apply, mul_colMat_apply]
  have hrow : G c j = (1 : Matrix (Fin n) (Fin n) R) c j := hg c j (Or.inl le_rfl)
  rw [hrow]
  by_cases hj : (j : ℕ) = c
  · have hjc : j = c := Fin.ext hj
    subst hjc
    rw [ite_eq_left rfl, Matrix.one_apply_eq, mul_one]
    by_cases hi : (i : ℕ) < j
    · rw [ite_eq_left hi]
      have hsum : ∑ k : Fin n, (if (k : ℕ) < j then G i k * w k else 0) = (G *ᵥ w) i := by
        rw [Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs with hk
        · rfl
        · rw [hg i k (Or.inr (not_lt.mp hk)),
            Matrix.one_apply_ne (fun h => by subst h; exact hk hi), zero_mul]
      rw [hsum, hGw]
    · rw [ite_eq_right hi]
      refine (Finset.sum_eq_zero fun k _ => ?_).symm
      split_ifs with hk
      · rw [hg i k (Or.inl (not_lt.mp hi)),
          Matrix.one_apply_ne (fun h => by subst h; exact hi hk), zero_mul]
      · rfl
  · have hjc : c ≠ j := fun h => hj (by rw [h])
    rw [ite_eq_right hj, Matrix.one_apply_ne hjc, mul_zero]
    split_ifs <;> rfl

/-! ### Upper unipotent matrices with trivial first columns -/

/-- Upper unitriangular matrices whose columns `≤ c` are those of the identity. -/
def IsUpperColId (c : ℕ) (M : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j : Fin n, ((j : ℕ) ≤ i ∨ (j : ℕ) ≤ c) → M i j = (1 : Matrix (Fin n) (Fin n) R) i j

theorem colUnit_mul_apply (c : Fin n) (v : Fin n → R) (M : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) :
    ((colUnit c v).val * M) i j = M i j + (if (i : ℕ) < c then v i * M c j else 0) := by
  rw [colUnit_val, add_mul, one_mul, Matrix.add_apply, colMat_mul_apply]

theorem mul_colUnit_apply (c : Fin n) (v : Fin n → R) (M : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) :
    (M * (colUnit c v).val) i j = M i j +
      (if (j : ℕ) = c then ∑ k : Fin n, (if (k : ℕ) < c then M i k * v k else 0) else 0) := by
  rw [colUnit_val, mul_add, mul_one, Matrix.add_apply, mul_colMat_apply]

theorem sum_lt_of_cols {c : ℕ} {M : Matrix (Fin n) (Fin n) R}
    (hM : ∀ i k : Fin n, (k : ℕ) < c → M i k = (1 : Matrix (Fin n) (Fin n) R) i k)
    (w : Fin n → R) (i : Fin n) :
    ∑ k : Fin n, (if (k : ℕ) < c then M i k * w k else 0) = if (i : ℕ) < c then w i else 0 := by
  rw [Finset.sum_eq_single i]
  · by_cases hi : (i : ℕ) < c
    · rw [ite_eq_left hi, ite_eq_left hi, hM i i hi, Matrix.one_apply_eq, one_mul]
    · rw [ite_eq_right hi, ite_eq_right hi]
  · intro k _ hk
    split_ifs with hkc
    · rw [hM i k hkc, Matrix.one_apply_ne (Ne.symm hk), zero_mul]
    · rfl
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Peeling off column `c + 1`: `u_{c+1}(-y₀) U`, with `y₀` the column `c + 1` of `U`, has
trivial columns `≤ c + 1` and the same rows `≥ c + 1` as `U`. -/
theorem isUpperColId_peel {c : ℕ} (col : Fin n) (hcol : (col : ℕ) = c + 1)
    {U : Matrix (Fin n) (Fin n) R} (hu : IsUpperColId c U) :
    IsUpperColId (c + 1) ((colUnit col (-fun i => U i col)).val * U) ∧
      ∀ i j : Fin n, c + 1 ≤ (i : ℕ) →
        ((colUnit col (-fun i => U i col)).val * U) i j = U i j := by
  have hentry : ∀ i j, ((colUnit col (-fun i => U i col)).val * U) i j =
      U i j + (if (i : ℕ) < col then -(U i col) * U col j else 0) := by
    intro i j
    rw [colUnit_mul_apply]
    rfl
  have hcolj : ∀ j : Fin n, (j : ℕ) ≤ c → U col j = 0 := by
    intro j hj
    rw [hu col j (Or.inr hj), Matrix.one_apply_ne]
    intro e
    rw [e] at hcol
    omega
  refine ⟨fun i j hij => ?_, fun i j hi => ?_⟩
  · rw [hentry]
    by_cases hj : (j : ℕ) ≤ c
    · rw [hu i j (Or.inr hj), hcolj j hj, mul_zero, ite_self, add_zero]
    · by_cases hjc : (j : ℕ) = c + 1
      · have hjcol : j = col := Fin.ext (by omega)
        subst hjcol
        rw [hu j j (Or.inl le_rfl), Matrix.one_apply_eq, mul_one]
        by_cases hi : (i : ℕ) < j
        · rw [ite_eq_left hi, add_neg_cancel, Matrix.one_apply_ne]
          intro e
          rw [e] at hi
          omega
        · rw [ite_eq_right hi, add_zero, hu i j (Or.inl (by omega))]
      · have hji : (j : ℕ) ≤ i := by omega
        rw [ite_eq_right (by omega), add_zero, hu i j (Or.inl hji)]
  · rw [hentry, ite_eq_right (by omega), add_zero]

/-- Conjugating by a column element keeps trivial columns `≤ c + 1` and the rows `≥ c + 1`. -/
theorem isUpperColId_conj {c : ℕ} (col : Fin n) (hcol : (col : ℕ) = c + 1)
    {U : Matrix (Fin n) (Fin n) R} (hu : IsUpperColId (c + 1) U) (z : Fin n → R) :
    IsUpperColId (c + 1) ((colUnit col z).val * U * (colUnit col (-z)).val) ∧
      ∀ i j : Fin n, c + 1 ≤ (i : ℕ) →
        ((colUnit col z).val * U * (colUnit col (-z)).val) i j = U i j := by
  set M := (colUnit col z).val * U with hM
  have hMentry : ∀ i k, M i k = U i k + (if (i : ℕ) < col then z i * U col k else 0) :=
    fun i k => colUnit_mul_apply col z U i k
  have hcolk : ∀ k : Fin n, (k : ℕ) < col → U col k = 0 := by
    intro k hk
    rw [hu col k (Or.inr (by omega)), Matrix.one_apply_ne]
    intro e
    rw [e] at hk
    omega
  have hMcols : ∀ i k : Fin n, (k : ℕ) < col → M i k = (1 : Matrix (Fin n) (Fin n) R) i k := by
    intro i k hk
    rw [hMentry, hu i k (Or.inr (by omega)), hcolk k hk, mul_zero, ite_self, add_zero]
  have hentry : ∀ i j, (M * (colUnit col (-z)).val) i j =
      U i j + (if (i : ℕ) < col then z i * U col j else 0) +
        (if (j : ℕ) = col then (if (i : ℕ) < col then -z i else 0) else 0) := by
    intro i j
    rw [mul_colUnit_apply, sum_lt_of_cols hMcols, hMentry]
    rfl
  refine ⟨fun i j hij => ?_, fun i j hi => ?_⟩
  · rw [hentry]
    by_cases hj : (j : ℕ) ≤ c
    · rw [hu i j (Or.inr (by omega)), hcolk j (by omega), mul_zero, ite_self, add_zero,
        ite_eq_right (by omega), add_zero]
    · by_cases hjc : (j : ℕ) = c + 1
      · have hjcol : j = col := Fin.ext (by omega)
        subst hjcol
        rw [hu j j (Or.inl le_rfl), Matrix.one_apply_eq, mul_one, ite_eq_left rfl]
        by_cases hi : (i : ℕ) < j
        · rw [ite_eq_left hi, ite_eq_left hi, add_assoc, add_neg_cancel, add_zero,
            hu i j (Or.inr (by omega))]
        · rw [ite_eq_right hi, ite_eq_right hi, add_zero, add_zero, hu i j (Or.inr (by omega))]
      · have hji : (j : ℕ) ≤ i := by omega
        rw [ite_eq_right (by omega), ite_eq_right (by omega), add_zero, add_zero, hu i j (Or.inl hji)]
  · rw [hentry, ite_eq_right (show ¬((i : ℕ) < col) by omega), add_zero,
      ite_eq_right (show ¬((i : ℕ) < col) by omega), ite_self, add_zero]

/-! ### Change of ring and continuity -/

section Map

variable {S : Type*} [CommRing S] (f : R →+* S)

theorem map_colUnit (c : Fin n) (v : Fin n → R) :
    Matrix.GeneralLinearGroup.map f (colUnit c v) = colUnit c (fun i => f (v i)) := by
  apply Units.ext
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, colUnit_val, Matrix.add_apply, colMat_apply,
    map_add, Matrix.one_apply]
  split_ifs <;> simp

theorem map_blkUnit (m c : ℕ) (X : Fin n × Fin n → R) :
    Matrix.GeneralLinearGroup.map f (blkUnit m c X) = blkUnit m c (fun p => f (X p)) := by
  apply Units.ext
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, blkUnit_val, Matrix.add_apply, blkMat_apply,
    map_add, Matrix.one_apply]
  split_ifs <;> simp

theorem IsMir.map {c : ℕ} {M : Matrix (Fin n) (Fin n) R} (h : IsMir c M) :
    IsMir c (M.map f) := by
  intro i j hij
  rw [Matrix.map_apply, h i j hij, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem IsBlk.map {c : ℕ} {M : Matrix (Fin n) (Fin n) R} (h : IsBlk c M) :
    IsBlk c (M.map f) := by
  intro i j hij
  rw [Matrix.map_apply, h i j hij, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end Map

section Topology

variable [TopologicalSpace R] [IsTopologicalRing R]

omit [IsTopologicalRing R] in
theorem continuous_colMat (c : Fin n) : Continuous (colMat (R := R) c) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [colMat_apply]
  split_ifs
  · exact continuous_apply i
  · exact continuous_const

omit [IsTopologicalRing R] in
theorem continuous_blkMat (m c : ℕ) : Continuous (blkMat (R := R) (n := n) m c) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [blkMat_apply]
  split_ifs
  · exact continuous_apply (i, j)
  · exact continuous_const

theorem continuous_colUnit (c : Fin n) : Continuous (colUnit (R := R) c) := by
  rw [Units.continuous_iff]
  exact ⟨continuous_const.add (continuous_colMat c),
    continuous_const.sub (continuous_colMat c)⟩

theorem continuous_blkUnit (m c : ℕ) : Continuous (blkUnit (R := R) (n := n) m c) := by
  rw [Units.continuous_iff]
  exact ⟨continuous_const.add (continuous_blkMat m c),
    continuous_const.sub (continuous_blkMat m c)⟩

omit [IsTopologicalRing R] in
theorem continuous_updateCol (c : Fin n) :
    Continuous (fun p : (Fin n × Fin n → R) × (Fin n → R) => updateCol p.1 c p.2) := by
  refine continuous_pi fun q => ?_
  simp only [updateCol]
  split_ifs
  · exact (continuous_apply q.1).comp continuous_snd
  · exact (continuous_apply q).comp continuous_fst

omit [IsTopologicalRing R] in
theorem continuous_truncVec (m : ℕ) : Continuous (truncVec (R := R) (n := n) m) := by
  refine continuous_pi fun i => ?_
  simp only [truncVec]
  split_ifs
  · exact continuous_apply i
  · exact continuous_const

end Topology

end Langlands.Automorphic.CuspidalWhittaker
