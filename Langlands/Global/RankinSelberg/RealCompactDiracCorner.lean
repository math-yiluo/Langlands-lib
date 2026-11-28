import Langlands.Representation.Archimedean.RealTiedMinorProduct
import Langlands.Representation.Archimedean.ComplexLowerUnipotentRestriction
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
# Lower-right corner minors of orthogonal matrices

For a real `n × n` matrix `X` and `l ≤ n`, `corner X l` is the minor of `X` on the rows and
columns `l, …, n - 1`. The module proves that minors of orthogonal matrices have absolute value
at most `1`, the behaviour of corner minors under left multiplication by upper triangular
matrices, that nonvanishing corner minors give the Library's `CornerNonzero`, and a bound for
the lower unipotent factor of an orthogonal matrix on the big cell: if `X = b L` with `b`
upper triangular and `L` lower unipotent, then `|L i j| ≤ (1 + n! 2ⁿ) / |corner X i|`.
-/

noncomputable section

open Finset Matrix
open scoped Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealCompactDirac

open Langlands.Archimedean Langlands.Archimedean.MatrixMinor
open Langlands.Archimedean.RealTiedMinorProduct (IsBottom minor_upper_mul)
open Langlands.Archimedean.LowerUnipotentRestriction

variable {n : ℕ}

/-! ## Tails and corner minors -/

/-- The positions `l, …, n - 1`. -/
def tail (n l : ℕ) : Finset (Fin n) := univ.filter fun i => l ≤ (i : ℕ)

theorem mem_tail {l : ℕ} {i : Fin n} : i ∈ tail n l ↔ l ≤ (i : ℕ) := by
  simp [tail]

theorem isBottom_tail (l : ℕ) : IsBottom (tail n l) := fun _ _ hij hi =>
  mem_tail.2 (le_trans (mem_tail.1 hi) (Fin.le_def.1 hij))

theorem tail_zero : tail n 0 = univ := by
  ext i
  simp [mem_tail]

theorem tail_of_le {l : ℕ} (hl : n ≤ l) : tail n l = ∅ := by
  ext i
  simp only [mem_tail, Finset.notMem_empty, iff_false, not_le]
  exact lt_of_lt_of_le i.2 hl

/-- The lower-right corner minor of `X` on the positions `l, …, n - 1`. -/
def corner (X : Matrix (Fin n) (Fin n) ℝ) (l : ℕ) : ℝ := minor X (tail n l) (tail n l)

theorem corner_zero (X : Matrix (Fin n) (Fin n) ℝ) : corner X 0 = X.det := by
  rw [corner, tail_zero, minor_univ]

theorem corner_of_le (X : Matrix (Fin n) (Fin n) ℝ) {l : ℕ} (hl : n ≤ l) : corner X l = 1 := by
  rw [corner, tail_of_le hl, minor_empty]

/-- Left multiplication by an upper triangular matrix multiplies a corner minor by the product
of the corresponding diagonal entries. -/
theorem corner_upper_mul {b : Matrix (Fin n) (Fin n) ℝ} (hb : b.IsUpperTriangular)
    (X : Matrix (Fin n) (Fin n) ℝ) (l : ℕ) :
    corner (b * X) l = (∏ i ∈ tail n l, b i i) * corner X l :=
  minor_upper_mul hb (isBottom_tail l) X _

theorem corner_diagonal_mul (d : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℝ) (l : ℕ) :
    corner (Matrix.diagonal d * X) l = (∏ i ∈ tail n l, d i) * corner X l :=
  minor_diagonal_mul d X _ _

/-- The corner minors of a lower unipotent matrix are `1`. -/
theorem corner_of_isLowerUnipotent {L : Matrix (Fin n) (Fin n) ℝ} (hL : IsLowerUnipotent L)
    (l : ℕ) : corner L l = 1 := by
  rw [corner, minor_of_isLowerTriangular (fun i j hij => hL.1 i j hij)]
  exact Finset.prod_eq_one fun i _ => hL.2 i

/-- If `X = b L` with `b` upper triangular and `L` lower unipotent, the corner minors of `X`
are the products of the corresponding diagonal entries of `b`. -/
theorem corner_eq_prod {X b L : Matrix (Fin n) (Fin n) ℝ} (hb : b.IsUpperTriangular)
    (hL : IsLowerUnipotent L) (hX : X = b * L) (l : ℕ) :
    corner X l = ∏ i ∈ tail n l, b i i := by
  rw [hX, corner_upper_mul hb, corner_of_isLowerUnipotent hL, mul_one]

/-- `tail l = {l} ∪ tail (l + 1)` for `l < n`. -/
theorem tail_eq_insert {l : ℕ} (hl : l < n) :
    tail n l = insert ⟨l, hl⟩ (tail n (l + 1)) := by
  ext i
  simp only [mem_tail, Finset.mem_insert, Fin.ext_iff]
  omega

theorem notMem_tail_succ {l : ℕ} (hl : l < n) : (⟨l, hl⟩ : Fin n) ∉ tail n (l + 1) := by
  simp [mem_tail]

/-- Consecutive corner minors of `X = b L` differ by a diagonal entry of `b`. -/
theorem corner_eq_mul_succ {X b L : Matrix (Fin n) (Fin n) ℝ} (hb : b.IsUpperTriangular)
    (hL : IsLowerUnipotent L) (hX : X = b * L) {l : ℕ} (hl : l < n) :
    corner X l = b ⟨l, hl⟩ ⟨l, hl⟩ * corner X (l + 1) := by
  rw [corner_eq_prod hb hL hX, corner_eq_prod hb hL hX, tail_eq_insert hl,
    Finset.prod_insert (notMem_tail_succ hl)]

/-! ## Minors of orthogonal matrices -/

/-- The squares of the minors of an orthogonal matrix with a fixed row set sum to `1`. -/
theorem sum_minor_sq {X : Matrix (Fin n) (Fin n) ℝ} (hX : X * Xᵀ = 1) (A : Finset (Fin n)) :
    ∑ C ∈ powersetCard A.card (univ : Finset (Fin n)), minor X A C ^ 2 = 1 := by
  have h := minor_mul X Xᵀ (A := A) (B := A) rfl rfl
  rw [hX, minor_one, if_pos rfl] at h
  rw [h]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [minor_transpose, sq]

/-- Minors of an orthogonal matrix have absolute value at most `1`. -/
theorem abs_minor_le_one {X : Matrix (Fin n) (Fin n) ℝ} (hX : X * Xᵀ = 1)
    {A B : Finset (Fin n)} (hAB : A.card = B.card) : |minor X A B| ≤ 1 := by
  have hB : B ∈ powersetCard A.card (univ : Finset (Fin n)) :=
    mem_powersetCard.2 ⟨subset_univ _, hAB.symm⟩
  have hle : minor X A B ^ 2 ≤ 1 := by
    rw [← sum_minor_sq hX A]
    exact Finset.single_le_sum (f := fun C => minor X A C ^ 2) (fun C _ => sq_nonneg _) hB
  have h1 : |minor X A B| ^ 2 ≤ 1 ^ 2 := by rwa [sq_abs, one_pow]
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) zero_le_one two_ne_zero).1 h1

theorem abs_corner_le_one {X : Matrix (Fin n) (Fin n) ℝ} (hX : X * Xᵀ = 1) (l : ℕ) :
    |corner X l| ≤ 1 :=
  abs_minor_le_one hX rfl

/-! ## Nonvanishing corner minors -/

theorem tail_map_succ (m l : ℕ) :
    (tail m l).map (Fin.succOrderEmb m).toEmbedding = tail (m + 1) (l + 1) := by
  ext i
  simp only [Finset.mem_map, mem_tail, RelEmbedding.coe_toEmbedding, Fin.coe_succOrderEmb]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simp only [Fin.val_succ]
    omega
  · intro hi
    refine ⟨i.pred (fun h => by simp [h] at hi), ?_, Fin.succ_pred _ _⟩
    have := Fin.val_pred i (fun h => by simp [h] at hi)
    omega

theorem corner_submatrix_succ {m : ℕ} (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (l : ℕ) :
    corner (X.submatrix Fin.succ Fin.succ) l = corner X (l + 1) := by
  have h := minor_submatrix_orderEmb (Fin.succOrderEmb m) X (tail m l) (tail m l)
  rw [Fin.coe_succOrderEmb, tail_map_succ] at h
  exact h

/-- Nonvanishing corner minors give the Library's recursive `CornerNonzero`. -/
theorem cornerNonzero_of_corner_ne_zero : ∀ {m : ℕ} {X : Matrix (Fin m) (Fin m) ℝ},
    (∀ l < m, corner X l ≠ 0) → CornerNonzero m X
  | 0, _, _ => trivial
  | m + 1, X, h => by
    refine ⟨?_, cornerNonzero_of_corner_ne_zero fun l hl => ?_⟩
    · rw [← corner_zero]
      exact h 0 (Nat.succ_pos m)
    · rw [corner_submatrix_succ]
      exact h (l + 1) (Nat.succ_lt_succ hl)

/-! ## The lower unipotent factor on the big cell -/

/-- The entry `(j, i)` matrix unit plus the identity: right multiplication adds column `j` to
column `i`. -/
def addColumn (j i : Fin n) : Matrix (Fin n) (Fin n) ℝ := 1 + Matrix.single j i 1

theorem mul_addColumn_apply (Y : Matrix (Fin n) (Fin n) ℝ) (j i r c : Fin n) :
    (Y * addColumn j i) r c = Y r c + if c = i then Y r j else 0 := by
  rw [addColumn, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  congr 1
  by_cases hc : c = i
  · subst hc
    rw [Matrix.mul_single_apply_same, mul_one, if_pos rfl]
  · rw [if_neg hc, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Matrix.single_apply, if_neg (fun h => hc h.2.symm), mul_zero]

/-- For a lower unipotent `L` and `j < i`, the corner minor at `i` of `L` with column `j` added
to column `i` is `1 + L i j`. -/
theorem corner_lower_mul_addColumn {L : Matrix (Fin n) (Fin n) ℝ} (hL : IsLowerUnipotent L)
    {i j : Fin n} (hji : j < i) :
    corner (L * addColumn j i) (i : ℕ) = 1 + L i j := by
  classical
  let Z : Matrix (Fin n) (Fin n) ℝ := fun r c =>
    if (i : ℕ) ≤ (r : ℕ) then (L * addColumn j i) r c else (1 : Matrix (Fin n) (Fin n) ℝ) r c
  have hZ : Z.IsLowerTriangular := by
    intro r c hrc
    change r < c at hrc
    simp only [Z]
    split_ifs with hr
    · rw [mul_addColumn_apply, hL.1 r c hrc, zero_add, if_neg]
      intro hci
      subst hci
      exact absurd (lt_of_le_of_lt hr hrc) (lt_irrefl _)
    · exact Matrix.one_apply_ne (ne_of_lt hrc)
  have hcongr : corner (L * addColumn j i) (i : ℕ) = minor Z (tail n i) (tail n i) :=
    minor_congr fun r hr c _ => by
      simp only [Z, if_pos (mem_tail.1 hr)]
  rw [hcongr, minor_of_isLowerTriangular hZ, tail_eq_insert i.2,
    Finset.prod_insert (notMem_tail_succ i.2)]
  have hi : (⟨(i : ℕ), i.2⟩ : Fin n) = i := rfl
  rw [hi]
  have hrest : ∏ l ∈ tail n ((i : ℕ) + 1), Z l l = 1 := by
    refine Finset.prod_eq_one fun l hl => ?_
    have hil : (i : ℕ) + 1 ≤ (l : ℕ) := mem_tail.1 hl
    simp only [Z, if_pos (by omega : (i : ℕ) ≤ (l : ℕ)), mul_addColumn_apply, hL.2 l]
    rw [if_neg (fun h => by subst h; omega), add_zero]
  rw [hrest, mul_one]
  simp only [Z, if_pos le_rfl, mul_addColumn_apply, hL.2 i, if_true]

/-- Entries of an orthogonal matrix have absolute value at most `1`. -/
theorem abs_entry_le_one {X : Matrix (Fin n) (Fin n) ℝ} (hX : X * Xᵀ = 1) (r c : Fin n) :
    |X r c| ≤ 1 := by
  have hmem : X ∈ Matrix.unitaryGroup (Fin n) ℝ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hX
  have := entry_norm_bound_of_unitary hmem r c
  rwa [Real.norm_eq_abs] at this

/-- Every principal minor `minor Y A A` of a matrix with entries bounded by `2` is bounded by
`n! 2ⁿ`. -/
theorem abs_minor_le_of_entry_le_two {Y : Matrix (Fin n) (Fin n) ℝ}
    (hY : ∀ r c, |Y r c| ≤ 2) (A : Finset (Fin n)) :
    |minor Y A A| ≤ (n.factorial : ℝ) * 2 ^ n := by
  rw [minor_eq rfl rfl]
  have h := Matrix.det_le (A := Y.submatrix (A.orderEmbOfFin rfl) (A.orderEmbOfFin rfl))
    (abv := AbsoluteValue.abs) (x := (2 : ℝ)) fun r c => hY _ _
  simp only [Fintype.card_fin, nsmul_eq_mul] at h
  have hcard : A.card ≤ n := by
    simpa using Finset.card_le_univ A
  refine h.trans (mul_le_mul ?_ ?_ (by positivity) (by positivity))
  · exact_mod_cast Nat.factorial_le hcard
  · exact pow_le_pow_right₀ (by norm_num) hcard

/-- The constant `1 + n! 2ⁿ` of the entry bound for the lower unipotent factor. -/
def lowerConstant (n : ℕ) : ℝ := 1 + (n.factorial : ℝ) * 2 ^ n

theorem one_le_lowerConstant (n : ℕ) : 1 ≤ lowerConstant n := by
  unfold lowerConstant
  have : (0 : ℝ) ≤ (n.factorial : ℝ) * 2 ^ n := by positivity
  linarith

/-- **The lower unipotent factor on the big cell.** If an orthogonal `X` is `b L` with `b`
upper triangular and `L` lower unipotent, then for `j < i` the entry `L i j` is bounded by
`(1 + n! 2ⁿ) / |corner X i|`. -/
theorem abs_lower_entry_le {X b L : Matrix (Fin n) (Fin n) ℝ} (hX : X * Xᵀ = 1)
    (hb : b.IsUpperTriangular) (hL : IsLowerUnipotent L) (he : X = b * L)
    {i j : Fin n} (hji : j < i) (hc : corner X i ≠ 0) :
    |L i j| ≤ lowerConstant n / |corner X i| := by
  have h1 : corner (X * addColumn j i) (i : ℕ) = corner X i * (1 + L i j) := by
    rw [he, Matrix.mul_assoc, corner_upper_mul hb, corner_lower_mul_addColumn hL hji,
      corner_upper_mul hb, corner_of_isLowerUnipotent hL, mul_one]
  have hent : ∀ r c, |(X * addColumn j i) r c| ≤ 2 := by
    intro r c
    rw [mul_addColumn_apply]
    have h1 := abs_entry_le_one hX r c
    split_ifs
    · have h2 := abs_entry_le_one hX r j
      calc |X r c + X r j| ≤ |X r c| + |X r j| := abs_add_le _ _
        _ ≤ 2 := by linarith
    · rw [add_zero]
      linarith
  have h2 : |corner X i| * |1 + L i j| ≤ (n.factorial : ℝ) * 2 ^ n := by
    rw [← abs_mul, ← h1]
    exact abs_minor_le_of_entry_le_two hent _
  have hpos : 0 < |corner X i| := abs_pos.2 hc
  have hle1 : |corner X i| ≤ 1 := abs_corner_le_one hX _
  rw [le_div_iff₀ hpos, lowerConstant]
  have h3 : |L i j| ≤ |1 + L i j| + 1 := by
    calc |L i j| = |(1 + L i j) - 1| := by ring_nf
      _ ≤ |1 + L i j| + |(1 : ℝ)| := abs_sub _ _
      _ = |1 + L i j| + 1 := by rw [abs_one]
  calc |L i j| * |corner X i| ≤ (|1 + L i j| + 1) * |corner X i| :=
        mul_le_mul_of_nonneg_right h3 hpos.le
    _ = |corner X i| * |1 + L i j| + |corner X i| := by ring
    _ ≤ (n.factorial : ℝ) * 2 ^ n + 1 := add_le_add h2 hle1
    _ = 1 + (n.factorial : ℝ) * 2 ^ n := by ring

end Langlands.Global.RankinSelbergGlobal.RealCompactDirac
