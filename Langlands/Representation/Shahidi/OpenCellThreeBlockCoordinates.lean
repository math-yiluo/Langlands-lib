import Langlands.Representation.Shahidi.OpenCellPieces

/-! # Coordinates of the three-block open cell

Entry formulas for block sums, upper radical matrices, block Weyl elements and exchanged
radicals by the values of their indices, and the identity relating the two factorizations of
the open cell of the parabolic of type `(1, d + 1, t + 1)`: after reassociating the rank,
`diag(w' u'(z), 1) · w u'(Y) = diag(1, w'' u''(Y_a)) · w̃ u'(y)` with `Y = [Y_a | Y_b]`
(`Y_b` the last column) and `y = [Y_b - Y_a z; z]`. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

open Langlands.GeneralLinear

section Numeric

variable {R : Type*} [CommRing R]

/-- Entries of a block sum at arbitrary indices, by their values. -/
theorem blockSum_apply_val {a b : ℕ} (g : Langlands.GeneralLinear a R)
    (h : Langlands.GeneralLinear b R) (x y : Fin (a + b)) :
    blockSum (g, h) x y =
      if hx : x.val < a then
        (if hy : y.val < a then g ⟨x.val, hx⟩ ⟨y.val, hy⟩ else 0)
      else
        (if hy : y.val < a then 0 else
          h ⟨x.val - a, by have := x.isLt; omega⟩ ⟨y.val - a, by have := y.isLt; omega⟩) := by
  induction x using Fin.addCases with
  | left i =>
    induction y using Fin.addCases with
    | left j => simp
    | right j => simp
  | right i =>
    induction y using Fin.addCases with
    | left j => simp
    | right j => simp

/-- Entries of the upper radical matrix by their values. -/
theorem upper_apply_val (a b : ℕ) (X : Matrix (Fin a) (Fin b) R) (x y : Fin (a + b)) :
    upper a b R X x y =
      if x.val = y.val then 1 else
        if hx : x.val < a then
          (if hy : a ≤ y.val then X ⟨x.val, hx⟩ ⟨y.val - a, by have := y.isLt; omega⟩ else 0)
        else 0 := by
  induction x using Fin.addCases with
  | left i =>
    induction y using Fin.addCases with
    | left j =>
      simp only [upper_first_first, Fin.val_castAdd, Fin.is_lt]
      by_cases hij : i = j
      · subst hij; simp
      · have : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
        simp [hij, this]
    | right j =>
      simp only [upper_first_second, Fin.val_castAdd, Fin.val_natAdd, Fin.is_lt]
      have : (i : ℕ) ≠ a + j := by have := i.isLt; omega
      simp [this]
  | right i =>
    induction y using Fin.addCases with
    | left j =>
      simp only [upper_second_first, Fin.val_natAdd, Fin.val_castAdd]
      have : a + (i : ℕ) ≠ j := by have := j.isLt; omega
      simp [this]
    | right j =>
      simp only [upper_second_second, Fin.val_natAdd]
      by_cases hij : i = j
      · subst hij; simp
      · have : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
        simp [hij, this]

theorem swapRank_apply (m n : ℕ) (g : Langlands.GeneralLinear (n + m) R) (x y : Fin (m + n)) :
    swapRank m n R g x y = g (Fin.cast (Nat.add_comm m n) x) (Fin.cast (Nat.add_comm m n) y) :=
  rfl

theorem blockWeylPermutation_symm_val (m n : ℕ) (x : Fin (m + n)) :
    ((blockWeylPermutation m n).symm x).val = if x.val < m then x.val + n else x.val - m := by
  induction x using Fin.addCases with
  | left i =>
    rw [blockWeylPermutation_symm_first]
    simp
  | right i =>
    rw [blockWeylPermutation_symm_second]
    simp

theorem blockWeylPermutation_val (m n : ℕ) (y : Fin (m + n)) :
    (blockWeylPermutation m n y).val = if y.val < n then m + y.val else y.val - n := by
  have h := blockWeylPermutation_symm_val m n (blockWeylPermutation m n y)
  rw [Equiv.symm_apply_apply] at h
  have hy := y.isLt
  have hp := (blockWeylPermutation m n y).isLt
  split_ifs at h ⊢ with h1 h2 h2 <;> omega

theorem blockWeyl_apply_val (m n : ℕ) (x y : Fin (m + n)) :
    blockWeyl m n R x y =
      if (if y.val < n then m + y.val else y.val - n) = x.val then 1 else 0 := by
  simp only [blockWeyl_entry, Fin.ext_iff, blockWeylPermutation_val]

theorem blockWeyl_mul_apply (m n : ℕ) (g : Langlands.GeneralLinear (m + n) R) (x y : Fin (m + n)) :
    (blockWeyl m n R * g) x y = g ((blockWeylPermutation m n).symm x) y := by
  rw [blockWeyl, permutation_mul_entry]
  rfl

theorem one_apply_gl {n : ℕ} (i j : Fin n) :
    (1 : Langlands.GeneralLinear n R) i j = if i = j then 1 else 0 := by
  change (1 : Matrix (Fin n) (Fin n) R) i j = _
  rw [Matrix.one_apply]

/-- Entries of `diag(1, U) u(Y) = [[1, Y], [0, U]]`. -/
theorem blockSum_one_mul_upper_apply {a b : ℕ} (U : Langlands.GeneralLinear b R)
    (Y : Matrix (Fin a) (Fin b) R) (x y : Fin (a + b)) :
    (blockSum ((1 : Langlands.GeneralLinear a R), U) * upper a b R Y) x y =
      if x.val < a then upper a b R Y x y
      else (if hy : y.val < a then 0 else
        U ⟨x.val - a, by have := x.isLt; omega⟩ ⟨y.val - a, by have := y.isLt; omega⟩) := by
  rw [mul_apply_split]
  induction x using Fin.addCases with
  | left i =>
    simp only [blockSum_apply_left, blockSum_apply_left_right, zero_mul, Finset.sum_const_zero,
      add_zero, one_apply_gl, ite_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      Fin.val_castAdd, Fin.is_lt]
  | right i =>
    simp only [blockSum_apply_right_left, zero_mul, Finset.sum_const_zero, zero_add,
      blockSum_apply_right, Fin.val_natAdd]
    have hn : ¬ (a + (i : ℕ) < a) := by omega
    simp only [hn, ite_false]
    induction y using Fin.addCases with
    | left j =>
      simp
    | right j =>
      simp only [upper_second_second, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, Fin.val_natAdd]
      have hn2 : ¬ (a + (j : ℕ) < a) := by omega
      simp only [hn2, dite_false, Nat.add_sub_cancel_left, Fin.eta]

/-- Entries of `diag(U, 1) u(y) = [[U, U y], [0, 1]]`. -/
theorem blockSum_mul_one_upper_apply {a b : ℕ} (U : Langlands.GeneralLinear a R)
    (y : Matrix (Fin a) (Fin b) R) (x z : Fin (a + b)) :
    (blockSum (U, (1 : Langlands.GeneralLinear b R)) * upper a b R y) x z =
      if hx : x.val < a then
        (if hz : z.val < a then U ⟨x.val, hx⟩ ⟨z.val, hz⟩ else
          ∑ p : Fin a, U ⟨x.val, hx⟩ p * y p ⟨z.val - a, by have := z.isLt; omega⟩)
      else (if x.val = z.val then 1 else 0) := by
  rw [mul_apply_split]
  induction x using Fin.addCases with
  | left i =>
    simp only [blockSum_apply_left, blockSum_apply_left_right, zero_mul, Finset.sum_const_zero,
      add_zero, Fin.val_castAdd, Fin.is_lt, dite_true]
    induction z using Fin.addCases with
    | left j =>
      simp only [upper_first_first, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, Fin.val_castAdd, Fin.is_lt, dite_true]
    | right j =>
      simp only [upper_first_second, Fin.val_natAdd]
      have hn : ¬ (a + (j : ℕ) < a) := by omega
      simp only [hn, dite_false]
      refine Finset.sum_congr rfl fun p _ => ?_
      congr 2
      ext
      simp
  | right i =>
    simp only [blockSum_apply_right_left, zero_mul, Finset.sum_const_zero, zero_add,
      blockSum_apply_right, Fin.val_natAdd, one_apply_gl, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have hn : ¬ (a + (i : ℕ) < a) := by omega
    simp only [hn, dite_false]
    rw [upper_apply_val]
    induction z using Fin.addCases with
    | left j =>
      simp only [Fin.val_natAdd, Fin.val_castAdd]
      have h1 : a + (i : ℕ) ≠ j := by have := j.isLt; omega
      simp [h1]
    | right j =>
      simp only [Fin.val_natAdd]
      by_cases hij : (i : ℕ) = j
      · simp [hij]
      · simp [hij]

/-- A row of `u(A) v`, for a row of the first block. -/
theorem sum_upper_mul_castAdd {a b : ℕ} (A : Matrix (Fin a) (Fin b) R) (v : Fin (a + b) → R)
    (i : Fin a) :
    ∑ p : Fin (a + b), upper a b R A (i.castAdd b) p * v p =
      v (i.castAdd b) + ∑ c : Fin b, A i c * v (c.natAdd a) := by
  rw [Fin.sum_univ_add]
  simp [upper_first_first, upper_first_second]

theorem intertwiningUnipotent_apply (m n : ℕ) (Y : Matrix (Fin n) (Fin m) R) (x y : Fin (m + n)) :
    intertwiningUnipotent m n R Y x y =
      upper n m R Y (Fin.cast (Nat.add_comm m n) x) (Fin.cast (Nat.add_comm m n) y) :=
  rfl

/-- A row of `u'(A) v` for the exchanged radical. -/
theorem sum_intertwiningUnipotent_row (d t : ℕ) (A : Matrix (Fin (t + 1)) (Fin (d + 1)) R)
    (v : Fin ((d + 1) + (t + 1)) → R) (i : ℕ) (hi : i < (d + 1) + (t + 1)) :
    ∑ x, intertwiningUnipotent (d + 1) (t + 1) R A ⟨i, hi⟩ x * v x =
      if h : i < t + 1 then
        v ⟨i, hi⟩ + ∑ b : Fin (d + 1), A ⟨i, h⟩ b * v ⟨t + 1 + b.val, by have := b.isLt; omega⟩
      else v ⟨i, hi⟩ := by
  rw [← (finCongr (Nat.add_comm (t + 1) (d + 1))).sum_comp]
  simp only [intertwiningUnipotent_apply, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]
  split_ifs with h
  · have e : Fin.cast (Nat.add_comm (d + 1) (t + 1)) (⟨i, hi⟩ : Fin ((d + 1) + (t + 1))) =
        Fin.castAdd (d + 1) ⟨i, h⟩ := Fin.ext rfl
    rw [e, sum_upper_mul_castAdd]
    congr 1
  · have e : Fin.cast (Nat.add_comm (d + 1) (t + 1)) (⟨i, hi⟩ : Fin ((d + 1) + (t + 1))) =
        Fin.natAdd (t + 1) ⟨i - (t + 1), by omega⟩ := Fin.ext (by simp; omega)
    rw [e, Fin.sum_univ_add]
    simp only [upper_second_first, zero_mul, Finset.sum_const_zero, zero_add,
      upper_second_second, ite_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    congr 1
    ext
    simp
    omega

end Numeric

section ThreeBlockCoordinates

variable {R : Type*} [CommRing R] (d t : ℕ)

/-- The first `d + 1` columns of a matrix with `(0 + 1) + (d + 1)` columns. -/
def headColumns (Y : Matrix (Fin (t + 1)) (Fin ((0 + 1) + (d + 1))) R) :
    Matrix (Fin (t + 1)) (Fin (d + 1)) R :=
  fun a b => Y a ⟨b.val, by have := b.isLt; omega⟩

/-- The column `[Y_b - Y_a z; z]` of the outer coordinates of the second factorization. -/
def shearColumn (Y : Matrix (Fin (t + 1)) (Fin ((0 + 1) + (d + 1))) R)
    (z : Matrix (Fin (d + 1)) (Fin (0 + 1)) R) : Matrix (Fin ((d + 1) + (t + 1))) (Fin (0 + 1)) R :=
  fun i _ => if h : i.val < t + 1 then
      Y ⟨i.val, h⟩ ⟨d + 1, by omega⟩ - ∑ b : Fin (d + 1), headColumns d t Y ⟨i.val, h⟩ b * z b 0
    else z ⟨i.val - (t + 1), by have := i.isLt; omega⟩ 0

/-- **The unipotent parts of the two factorizations of the three-block cell agree.** -/
theorem reindex_swapRank_unipotent (Y : Matrix (Fin (t + 1)) (Fin ((0 + 1) + (d + 1))) R)
    (z : Matrix (Fin (d + 1)) (Fin (0 + 1)) R) :
    GeneralLinear.reindex (finCongr (Nat.add_assoc (0 + 1) (d + 1) (t + 1)))
        (swapRank ((0 + 1) + (d + 1)) (t + 1) R
          (blockSum ((1 : Langlands.GeneralLinear (t + 1) R),
              intertwiningUnipotent (0 + 1) (d + 1) R z) *
            upper (t + 1) ((0 + 1) + (d + 1)) R Y)) =
      swapRank (0 + 1) ((d + 1) + (t + 1)) R
        (blockSum (intertwiningUnipotent (d + 1) (t + 1) R (headColumns d t Y),
            (1 : Langlands.GeneralLinear (0 + 1) R)) *
          upper ((d + 1) + (t + 1)) (0 + 1) R (shearColumn d t Y z)) := by
  apply Units.ext
  ext i j
  change (blockSum ((1 : Langlands.GeneralLinear (t + 1) R),
              intertwiningUnipotent (0 + 1) (d + 1) R z) *
            upper (t + 1) ((0 + 1) + (d + 1)) R Y) (Fin.cast (by omega) i) (Fin.cast (by omega) j) =
    (blockSum (intertwiningUnipotent (d + 1) (t + 1) R (headColumns d t Y),
            (1 : Langlands.GeneralLinear (0 + 1) R)) *
          upper ((d + 1) + (t + 1)) (0 + 1) R (shearColumn d t Y z))
      (Fin.cast (by omega) i) (Fin.cast (by omega) j)
  rw [blockSum_one_mul_upper_apply, blockSum_mul_one_upper_apply]
  have hiN := i.isLt
  have hjN := j.isLt
  simp only [Fin.val_cast]
  by_cases hjl : (j : ℕ) < d + 1 + (t + 1)
  · simp only [hjl, dite_true]
    simp only [intertwiningUnipotent_apply, upper_apply_val, Fin.val_cast, headColumns, Fin.val_mk]
    by_cases hil : (i : ℕ) < d + 1 + (t + 1)
    · simp only [hil, dite_true]
      by_cases hit : (i : ℕ) < t + 1
      · simp only [hit, ite_true, dite_true]
      · simp only [hit, ite_false, dite_false]
        by_cases hjt : (j : ℕ) < t + 1
        · have : (i : ℕ) ≠ j := by omega
          simp [hjt, this]
        · have hd : ¬ (d + 1 ≤ (j : ℕ) - (t + 1)) := by omega
          by_cases hij : (i : ℕ) = j
          · have : (i : ℕ) - (t + 1) = (j : ℕ) - (t + 1) := by omega
            simp [hjt, hij]
          · have : (i : ℕ) - (t + 1) ≠ (j : ℕ) - (t + 1) := by omega
            simp [hjt, hij, this, hd]
    · have hit : ¬ (i : ℕ) < t + 1 := by omega
      simp only [hil, dite_false, hit, ite_false]
      have hij : (i : ℕ) ≠ j := by omega
      by_cases hjt : (j : ℕ) < t + 1
      · simp [hjt, hij]
      · have hd : ¬ ((i : ℕ) - (t + 1) < d + 1) := by omega
        have : (i : ℕ) - (t + 1) ≠ (j : ℕ) - (t + 1) := by omega
        simp [hjt, hij, this, hd]
  · have hjv : (j : ℕ) = d + 1 + (t + 1) := by omega
    have hjt : ¬ (j : ℕ) < t + 1 := by omega
    simp only [hjl, dite_false, hjt]
    by_cases hil : (i : ℕ) < d + 1 + (t + 1)
    · simp only [hil, dite_true]
      rw [sum_intertwiningUnipotent_row]
      have hz : ∀ b : Fin (d + 1), shearColumn d t Y z ⟨t + 1 + b.val, by omega⟩
          ⟨(j : ℕ) - (d + 1 + (t + 1)), by omega⟩ = z b 0 := by
        intro b
        simp only [shearColumn]
        simp only [show ¬ (t + 1 + b.val < t + 1) by omega, dite_false]
        congr 1
        all_goals (ext; simp)
      simp only [hz]
      by_cases hit : (i : ℕ) < t + 1
      · simp only [hit, ite_true, dite_true]
        rw [upper_apply_val]
        simp only [Fin.val_cast]
        have hij : (i : ℕ) ≠ j := by omega
        have htj : t + 1 ≤ (j : ℕ) := by omega
        simp only [hij, ite_false, hit, dite_true, htj]
        simp only [shearColumn, hit, dite_true]
        have hc : (⟨(j : ℕ) - (t + 1), by omega⟩ : Fin ((0 + 1) + (d + 1))) =
            ⟨d + 1, by omega⟩ := Fin.ext (by simp; omega)
        rw [hc]
        ring
      · simp only [hit, ite_false, dite_false]
        simp only [intertwiningUnipotent_apply, upper_apply_val, Fin.val_cast]
        have hij : (i : ℕ) - (t + 1) ≠ (j : ℕ) - (t + 1) := by omega
        have hid : (i : ℕ) - (t + 1) < d + 1 := by omega
        have hjd : d + 1 ≤ (j : ℕ) - (t + 1) := by omega
        simp only [hij, ite_false, hid, dite_true, hjd]
        simp only [shearColumn, hit, dite_false]
        congr 1
        all_goals (ext; simp; try omega)
    · have hiv : (i : ℕ) = d + 1 + (t + 1) := by omega
      have hit : ¬ (i : ℕ) < t + 1 := by omega
      simp only [hil, dite_false, hit, ite_false]
      simp only [intertwiningUnipotent_apply, upper_apply_val, Fin.val_cast]
      have hd : ¬ ((i : ℕ) - (t + 1) < d + 1) := by omega
      have hij : (i : ℕ) = j := by omega
      have : (i : ℕ) - (t + 1) = (j : ℕ) - (t + 1) := by omega
      simp [hij]

/-- **The Weyl parts of the two factorizations of the three-block cell agree.** -/
theorem reindex_blockWeyl_mul_swapRank :
    GeneralLinear.reindex (finCongr (Nat.add_assoc (0 + 1) (d + 1) (t + 1)))
        (blockWeyl ((0 + 1) + (d + 1)) (t + 1) R *
          swapRank ((0 + 1) + (d + 1)) (t + 1) R
            (blockSum ((1 : Langlands.GeneralLinear (t + 1) R), blockWeyl (0 + 1) (d + 1) R))) =
      blockWeyl (0 + 1) ((d + 1) + (t + 1)) R *
        swapRank (0 + 1) ((d + 1) + (t + 1)) R
          (blockSum (blockWeyl (d + 1) (t + 1) R, (1 : Langlands.GeneralLinear (0 + 1) R))) := by
  apply Units.ext
  ext i j
  change (blockWeyl ((0 + 1) + (d + 1)) (t + 1) R *
          swapRank ((0 + 1) + (d + 1)) (t + 1) R
            (blockSum ((1 : Langlands.GeneralLinear (t + 1) R), blockWeyl (0 + 1) (d + 1) R)))
        (Fin.cast (by omega) i) (Fin.cast (by omega) j) = _
  rw [blockWeyl_mul_apply, blockWeyl_mul_apply, swapRank_apply, swapRank_apply, blockSum_apply_val,
    blockSum_apply_val]
  have hiN := i.isLt
  have hjN := j.isLt
  simp only [Fin.val_cast, blockWeylPermutation_symm_val, one_apply_gl, Fin.ext_iff,
    blockWeyl_apply_val]
  by_cases h1 : (i : ℕ) < 0 + 1 <;> by_cases h2 : (i : ℕ) < 0 + 1 + (d + 1) <;>
    by_cases h3 : (j : ℕ) < t + 1 <;> by_cases h4 : (j : ℕ) - (t + 1) < d + 1 <;>
    by_cases h5 : (j : ℕ) < d + 1 + (t + 1) <;>
    simp only [h1, h2, h3, h4, h5, ite_true, ite_false, dite_true, dite_false] <;>
    split_ifs <;> first | rfl | omega

theorem blockSum_mul_blockWeyl (m n : ℕ) (x : Langlands.GeneralLinear m R) :
    blockSum (x, (1 : Langlands.GeneralLinear n R)) * blockWeyl m n R =
      blockWeyl m n R * swapRank m n R (blockSum ((1 : Langlands.GeneralLinear n R), x)) := by
  rw [← blockWeyl_conjugate_blockSum m n R (1 : Langlands.GeneralLinear n R) x]
  group

theorem blockSum_one_mul_blockWeyl (m n : ℕ) (x : Langlands.GeneralLinear n R) :
    blockSum ((1 : Langlands.GeneralLinear m R), x) * blockWeyl m n R =
      blockWeyl m n R * swapRank m n R (blockSum (x, (1 : Langlands.GeneralLinear m R))) := by
  rw [← blockWeyl_conjugate_blockSum m n R x (1 : Langlands.GeneralLinear m R)]
  group

/-- **The two factorizations of the three-block open cell.** With `Y = [Y_a | Y_b]`, the element
`diag(w' u'(z), 1) w u'(Y)` of the first factorization is, after reassociating the rank, the
element `diag(1, w'' u''(Y_a)) w̃ u'(y)` of the second, for `y = [Y_b - Y_a z; z]`. -/
theorem reindex_threeBlock (Y : Matrix (Fin (t + 1)) (Fin ((0 + 1) + (d + 1))) R)
    (z : Matrix (Fin (d + 1)) (Fin (0 + 1)) R) :
    GeneralLinear.reindex (finCongr (Nat.add_assoc (0 + 1) (d + 1) (t + 1)))
        (blockSum (blockWeyl (0 + 1) (d + 1) R * intertwiningUnipotent (0 + 1) (d + 1) R z,
            (1 : Langlands.GeneralLinear (t + 1) R)) *
          (blockWeyl ((0 + 1) + (d + 1)) (t + 1) R *
            intertwiningUnipotent ((0 + 1) + (d + 1)) (t + 1) R Y)) =
      blockSum ((1 : Langlands.GeneralLinear (0 + 1) R),
          blockWeyl (d + 1) (t + 1) R * intertwiningUnipotent (d + 1) (t + 1) R (headColumns d t Y)) *
        (blockWeyl (0 + 1) ((d + 1) + (t + 1)) R *
          intertwiningUnipotent (0 + 1) ((d + 1) + (t + 1)) R (shearColumn d t Y z)) := by
  have hL : blockSum (blockWeyl (0 + 1) (d + 1) R * intertwiningUnipotent (0 + 1) (d + 1) R z,
            (1 : Langlands.GeneralLinear (t + 1) R)) *
          (blockWeyl ((0 + 1) + (d + 1)) (t + 1) R *
            intertwiningUnipotent ((0 + 1) + (d + 1)) (t + 1) R Y) =
      (blockWeyl ((0 + 1) + (d + 1)) (t + 1) R *
          swapRank ((0 + 1) + (d + 1)) (t + 1) R
            (blockSum ((1 : Langlands.GeneralLinear (t + 1) R), blockWeyl (0 + 1) (d + 1) R))) *
        swapRank ((0 + 1) + (d + 1)) (t + 1) R
          (blockSum ((1 : Langlands.GeneralLinear (t + 1) R),
              intertwiningUnipotent (0 + 1) (d + 1) R z) *
            upper (t + 1) ((0 + 1) + (d + 1)) R Y) := by
    rw [← mul_assoc, blockSum_mul_blockWeyl,
      show intertwiningUnipotent ((0 + 1) + (d + 1)) (t + 1) R Y =
        swapRank ((0 + 1) + (d + 1)) (t + 1) R (upper (t + 1) ((0 + 1) + (d + 1)) R Y) from rfl,
      map_mul]
    have e : blockSum ((1 : Langlands.GeneralLinear (t + 1) R),
          blockWeyl (0 + 1) (d + 1) R * intertwiningUnipotent (0 + 1) (d + 1) R z) =
        blockSum ((1 : Langlands.GeneralLinear (t + 1) R), blockWeyl (0 + 1) (d + 1) R) *
          blockSum ((1 : Langlands.GeneralLinear (t + 1) R),
            intertwiningUnipotent (0 + 1) (d + 1) R z) := by
      rw [← map_mul, Prod.mk_mul_mk, one_mul]
    rw [e, map_mul]
    group
  have hR : blockSum ((1 : Langlands.GeneralLinear (0 + 1) R),
          blockWeyl (d + 1) (t + 1) R * intertwiningUnipotent (d + 1) (t + 1) R (headColumns d t Y)) *
        (blockWeyl (0 + 1) ((d + 1) + (t + 1)) R *
          intertwiningUnipotent (0 + 1) ((d + 1) + (t + 1)) R (shearColumn d t Y z)) =
      (blockWeyl (0 + 1) ((d + 1) + (t + 1)) R *
          swapRank (0 + 1) ((d + 1) + (t + 1)) R
            (blockSum (blockWeyl (d + 1) (t + 1) R, (1 : Langlands.GeneralLinear (0 + 1) R)))) *
        swapRank (0 + 1) ((d + 1) + (t + 1)) R
          (blockSum (intertwiningUnipotent (d + 1) (t + 1) R (headColumns d t Y),
              (1 : Langlands.GeneralLinear (0 + 1) R)) *
            upper ((d + 1) + (t + 1)) (0 + 1) R (shearColumn d t Y z)) := by
    rw [← mul_assoc, blockSum_one_mul_blockWeyl,
      show intertwiningUnipotent (0 + 1) ((d + 1) + (t + 1)) R (shearColumn d t Y z) =
        swapRank (0 + 1) ((d + 1) + (t + 1)) R
          (upper ((d + 1) + (t + 1)) (0 + 1) R (shearColumn d t Y z)) from rfl, map_mul]
    have e : blockSum (blockWeyl (d + 1) (t + 1) R *
          intertwiningUnipotent (d + 1) (t + 1) R (headColumns d t Y),
          (1 : Langlands.GeneralLinear (0 + 1) R)) =
        blockSum (blockWeyl (d + 1) (t + 1) R, (1 : Langlands.GeneralLinear (0 + 1) R)) *
          blockSum (intertwiningUnipotent (d + 1) (t + 1) R (headColumns d t Y),
            (1 : Langlands.GeneralLinear (0 + 1) R)) := by
      rw [← map_mul, Prod.mk_mul_mk, one_mul]
    rw [e, map_mul]
    group
  rw [hL, hR, map_mul, reindex_blockWeyl_mul_swapRank, reindex_swapRank_unipotent]

end ThreeBlockCoordinates

end Langlands.Shahidi.OpenCell
