import Langlands.Representation.Shahidi.Geometry
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Valuation.Integers

/-! # The open-cell coordinate of a matrix of `GL_(r+t+2)` over a valued field

For a matrix `g` of size `r + t + 2` over a field, write `A(g)` for its lower left
`(t + 1) × (t + 1)` block (rows `r + 1, …, r + t + 1`, columns `0, …, t`) and `B(g)` for its lower
right `(t + 1) × (r + 1)` block. For `g ∈ GL_(r+t+2)(K)` with `A(g)` invertible,
`A(g)⁻¹ B(g)` is the coordinate `Y` of the decomposition `g = p w u'(Y)` of the open Bruhat
cell `P w U'` of the upper two-block parabolic `P` with blocks `(r + 1, t + 1)`. This module
proves that the condition "`A(g)` is invertible and `A(g)⁻¹ B(g)` has entries of valuation
`< γ`" is invariant under left multiplication by `P`, under right multiplication by the
matrices congruent to `1` modulo `γ` (for `γ ≤ 1`), and holds at `w u'(Y)` exactly when `Y`
has entries of valuation `< γ`. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Global.CuspidalPairEisenstein.OpenCellCutoff

open Matrix

section Indices

variable (r t : ℕ)

/-- The row `r + 1 + i` of the lower block. -/
def botIdx (i : Fin (t + 1)) : Fin (r + t + 2) := ⟨r + 1 + i, by omega⟩

/-- The row `j` of the upper block. -/
def topIdx (j : Fin (r + 1)) : Fin (r + t + 2) := ⟨j, by omega⟩

/-- The column `j` of the left block of size `t + 1`. -/
def leftIdx (j : Fin (t + 1)) : Fin (r + t + 2) := ⟨j, by omega⟩

/-- The column `t + 1 + j` of the right block of size `r + 1`. -/
def rightIdx (j : Fin (r + 1)) : Fin (r + t + 2) := ⟨t + 1 + j, by omega⟩

theorem botIdx_injective : Function.Injective (botIdx r t) := by
  intro i j h
  have := congrArg Fin.val h
  simp only [botIdx] at this
  exact Fin.ext (by omega)

theorem leftIdx_injective : Function.Injective (leftIdx r t) := by
  intro i j h
  have := congrArg Fin.val h
  simp only [leftIdx] at this
  exact Fin.ext this

theorem leftIdx_ne_rightIdx (i : Fin (t + 1)) (j : Fin (r + 1)) : leftIdx r t i ≠ rightIdx r t j := by
  intro h
  have := congrArg Fin.val h
  simp only [leftIdx, rightIdx] at this
  omega

theorem sum_rows {M : Type*} [AddCommMonoid M] (f : Fin (r + t + 2) → M) :
    ∑ l, f l = ∑ j : Fin (r + 1), f (topIdx r t j) + ∑ i : Fin (t + 1), f (botIdx r t i) := by
  rw [← (finCongr (show r + 1 + (t + 1) = r + t + 2 by omega)).sum_comp, Fin.sum_univ_add]
  rfl

theorem sum_cols {M : Type*} [AddCommMonoid M] (f : Fin (r + t + 2) → M) :
    ∑ l, f l = ∑ j : Fin (t + 1), f (leftIdx r t j) + ∑ j : Fin (r + 1), f (rightIdx r t j) := by
  rw [← (finCongr (show t + 1 + (r + 1) = r + t + 2 by omega)).sum_comp, Fin.sum_univ_add]
  rfl

end Indices

section Blocks

variable {K : Type*} [Field K] (r t : ℕ)

/-- The lower left `(t + 1) × (t + 1)` block `A(g)`. -/
def botLeft (g : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K) :
    Matrix (Fin (t + 1)) (Fin (t + 1)) K :=
  fun i j => g (botIdx r t i) (leftIdx r t j)

/-- The lower right `(t + 1) × (r + 1)` block `B(g)`. -/
def botRight (g : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K) :
    Matrix (Fin (t + 1)) (Fin (r + 1)) K :=
  fun i j => g (botIdx r t i) (rightIdx r t j)

/-- The lower right diagonal block of size `t + 1` for the row blocks `(r + 1, t + 1)`. -/
def botBot (g : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K) :
    Matrix (Fin (t + 1)) (Fin (t + 1)) K :=
  fun i j => g (botIdx r t i) (botIdx r t j)

/-- The open-cell coordinate `A(g)⁻¹ B(g)` (the Library inverse, which is `0` for a singular
`A(g)`). -/
def cellCoord (g : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K) :
    Matrix (Fin (t + 1)) (Fin (r + 1)) K :=
  (botLeft r t g)⁻¹ * botRight r t g

/-- The upper left `(t + 1) × (t + 1)` block of `k` for the column blocks `(t + 1, r + 1)`. -/
def kLL (k : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K) :
    Matrix (Fin (t + 1)) (Fin (t + 1)) K :=
  fun i j => k (leftIdx r t i) (leftIdx r t j)

/-- The lower left `(r + 1) × (t + 1)` block of `k` for the column blocks `(t + 1, r + 1)`. -/
def kRL (k : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K) :
    Matrix (Fin (r + 1)) (Fin (t + 1)) K :=
  fun i j => k (rightIdx r t i) (leftIdx r t j)

/-- The upper right `(t + 1) × (r + 1)` block of `k` for the column blocks `(t + 1, r + 1)`. -/
def kLR (k : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K) :
    Matrix (Fin (t + 1)) (Fin (r + 1)) K :=
  fun i j => k (leftIdx r t i) (rightIdx r t j)

/-- The lower right `(r + 1) × (r + 1)` block of `k` for the column blocks `(t + 1, r + 1)`. -/
def kRR (k : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  fun i j => k (rightIdx r t i) (rightIdx r t j)

variable {r t}

theorem botLeft_mul_of_lowerZero {p g : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K}
    (hp : ∀ i j, p (botIdx r t i) (topIdx r t j) = 0) :
    botLeft r t (p * g) = botBot r t p * botLeft r t g := by
  ext i j
  simp only [botLeft, botBot, Matrix.mul_apply]
  rw [sum_rows r t]
  simp [hp]

theorem botRight_mul_of_lowerZero {p g : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K}
    (hp : ∀ i j, p (botIdx r t i) (topIdx r t j) = 0) :
    botRight r t (p * g) = botBot r t p * botRight r t g := by
  ext i j
  simp only [botRight, botBot, Matrix.mul_apply]
  rw [sum_rows r t]
  simp [hp]

theorem botBot_mul_of_lowerZero {p g : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K}
    (hp : ∀ i j, p (botIdx r t i) (topIdx r t j) = 0) :
    botBot r t (p * g) = botBot r t p * botBot r t g := by
  ext i j
  simp only [botBot, Matrix.mul_apply]
  rw [sum_rows r t]
  simp [hp]

theorem botBot_one : botBot r t (1 : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K) = 1 := by
  ext i j
  simp only [botBot, Matrix.one_apply, (botIdx_injective r t).eq_iff]

/-- The lower right diagonal block of an invertible matrix with zero lower left block is
invertible. -/
theorem isUnit_det_botBot {p q : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K}
    (hp : ∀ i j, p (botIdx r t i) (topIdx r t j) = 0) (hpq : p * q = 1) :
    IsUnit (botBot r t p).det := by
  have h := congrArg Matrix.det (botBot_mul_of_lowerZero (g := q) hp)
  rw [hpq, botBot_one, Matrix.det_one, Matrix.det_mul] at h
  exact IsUnit.of_mul_eq_one _ h.symm

theorem botLeft_mul (g k : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K) :
    botLeft r t (g * k) = botLeft r t g * kLL r t k + botRight r t g * kRL r t k := by
  ext i j
  simp only [botLeft, botRight, kLL, kRL, Matrix.mul_apply, Matrix.add_apply]
  rw [sum_cols r t]

theorem botRight_mul (g k : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K) :
    botRight r t (g * k) = botLeft r t g * kLR r t k + botRight r t g * kRR r t k := by
  ext i j
  simp only [botRight, botLeft, kLR, kRR, Matrix.mul_apply, Matrix.add_apply]
  rw [sum_cols r t]

/-- Left multiplication by a matrix with zero lower left block and invertible lower right block
`D` multiplies `A` and `B` by `D` and leaves the coordinate `A⁻¹ B` unchanged. -/
theorem cellCoord_mul_of_lowerZero {p g : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K}
    (hp : ∀ i j, p (botIdx r t i) (topIdx r t j) = 0) (hD : IsUnit (botBot r t p).det) :
    cellCoord r t (p * g) = cellCoord r t g := by
  rw [cellCoord, cellCoord, botLeft_mul_of_lowerZero hp, botRight_mul_of_lowerZero hp,
    Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc _ (botBot r t p),
    Matrix.nonsing_inv_mul _ hD, Matrix.one_mul]

end Blocks

section Valuation

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation K Γ₀) (r t : ℕ)

/-- The open-cell condition of level `γ`: the block `A(g)` is invertible and the coordinate
`A(g)⁻¹ B(g)` has entries of valuation `< γ`. -/
def InCell (γ : Γ₀) (g : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K) : Prop :=
  (botLeft r t g).det ≠ 0 ∧ ∀ i j, v (cellCoord r t g i j) < γ

variable {v r t}

/-- The open-cell condition is invariant under left multiplication by an invertible matrix with
zero lower left block. -/
theorem inCell_mul_left_iff {γ : Γ₀} {p q g : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K}
    (hp : ∀ i j, p (botIdx r t i) (topIdx r t j) = 0) (hpq : p * q = 1) :
    InCell v r t γ (p * g) ↔ InCell v r t γ g := by
  have hD := isUnit_det_botBot hp hpq
  rw [InCell, InCell, cellCoord_mul_of_lowerZero hp hD, botLeft_mul_of_lowerZero hp,
    Matrix.det_mul]
  exact and_congr_left' ⟨fun h h0 => h (by rw [h0, mul_zero]),
    fun h => mul_ne_zero hD.ne_zero h⟩

/-- The ideal of the valuation integers of valuation `< γ`, for `γ ≠ 0`. -/
def ltIdeal (γ : Γ₀) (hγ : γ ≠ 0) : Ideal v.integer where
  carrier := {x | v (x : K) < γ}
  add_mem' {a b} ha hb := by
    change v ((a : K) + b) < γ
    exact v.map_add_lt ha hb
  zero_mem' := by
    change v (0 : K) < γ
    rw [v.map_zero]
    exact zero_lt_iff.mpr hγ
  smul_mem' c x hx := by
    change v ((c : K) * x) < γ
    rw [v.map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' c.2) hx

/-- A square matrix congruent to `1` modulo `γ ≤ 1` has a determinant of valuation `1` and an
inverse with integral entries. -/
theorem det_and_inv_of_close_one {n : ℕ} {γ : Γ₀} (hγ0 : γ ≠ 0) (hγ1 : γ ≤ 1)
    {M : Matrix (Fin n) (Fin n) K} (hM : ∀ i j, v (M i j - (1 : Matrix (Fin n) (Fin n) K) i j) < γ) :
    v M.det = 1 ∧ ∀ i j, v (M⁻¹ i j) ≤ 1 := by
  have hint : ∀ i j, v (M i j) ≤ 1 := by
    intro i j
    have e : M i j = (M i j - (1 : Matrix (Fin n) (Fin n) K) i j) +
        (1 : Matrix (Fin n) (Fin n) K) i j := by ring
    rw [e]
    refine le_trans (v.map_add _ _) (max_le (le_trans (hM i j).le hγ1) ?_)
    rw [Matrix.one_apply]
    split_ifs
    · rw [v.map_one]
    · rw [v.map_zero]
      exact zero_le_one' Γ₀
  let MO : Matrix (Fin n) (Fin n) v.integer := fun i j => ⟨M i j, hint i j⟩
  have hMO : MO.map v.integer.subtype = M := by
    ext i j
    rfl
  let I := ltIdeal (v := v) γ hγ0
  have hmap : MO.map (Ideal.Quotient.mk I) = 1 := by
    ext i j
    rw [Matrix.map_apply, Matrix.one_apply]
    have h1 : (if i = j then (1 : v.integer ⧸ I) else 0) =
        Ideal.Quotient.mk I ((1 : Matrix (Fin n) (Fin n) v.integer) i j) := by
      rw [Matrix.one_apply]
      split_ifs <;> simp
    rw [h1, Ideal.Quotient.eq]
    change v (((MO i j - (1 : Matrix (Fin n) (Fin n) v.integer) i j : v.integer) : K)) < γ
    have h2 : (((MO i j - (1 : Matrix (Fin n) (Fin n) v.integer) i j : v.integer) : K)) =
        M i j - (1 : Matrix (Fin n) (Fin n) K) i j := by
      rw [AddSubgroupClass.coe_sub]
      congr 1
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [h2]
    exact hM i j
  have hdet : Ideal.Quotient.mk I MO.det = Ideal.Quotient.mk I 1 := by
    rw [map_one, RingHom.map_det, RingHom.mapMatrix_apply, hmap, Matrix.det_one]
  rw [Ideal.Quotient.eq] at hdet
  have hdetK : (MO.det : K) = M.det := by
    rw [← hMO]
    exact RingHom.map_det v.integer.subtype MO
  have hlt : v (M.det - 1) < 1 := by
    have h := hdet
    change v (((MO.det - 1 : v.integer) : K)) < γ at h
    rw [AddSubgroupClass.coe_sub, hdetK, OneMemClass.coe_one] at h
    exact lt_of_lt_of_le h hγ1
  have hv1 : v M.det = 1 := by
    have e : M.det = 1 + (M.det - 1) := by ring
    rw [e]
    exact v.map_one_add_of_lt hlt
  refine ⟨hv1, fun i j => ?_⟩
  have hadj : M.adjugate = MO.adjugate.map v.integer.subtype := by
    rw [← hMO]
    exact (RingHom.map_adjugate v.integer.subtype MO).symm
  rw [Matrix.inv_def, Matrix.smul_apply, hadj, Matrix.map_apply, smul_eq_mul, v.map_mul,
    Ring.inverse_eq_inv', map_inv₀, hv1, inv_one, one_mul]
  exact (MO.adjugate i j).2

theorem map_mul_lt_of_lt {γ : Γ₀} {n m : ℕ} (hγ0 : γ ≠ 0)
    {c : Matrix (Fin n) (Fin m) K} (hc : ∀ i j, v (c i j) < γ)
    {k : Type*} {X : Matrix (Fin m) k K} (hX : ∀ i j, v (X i j) ≤ 1) (i : Fin n) (j : k) :
    v ((c * X) i j) < γ := by
  rw [Matrix.mul_apply]
  refine v.map_sum_lt hγ0 fun l _ => ?_
  rw [v.map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' (hX l j)) (hc i l)

theorem map_mul_lt_of_lt' {γ : Γ₀} {n m : ℕ} (hγ0 : γ ≠ 0)
    {X : Matrix (Fin n) (Fin m) K} (hX : ∀ i j, v (X i j) ≤ 1)
    {k : Type*} {c : Matrix (Fin m) k K} (hc : ∀ i j, v (c i j) < γ) (i : Fin n) (j : k) :
    v ((X * c) i j) < γ := by
  rw [Matrix.mul_apply]
  refine v.map_sum_lt hγ0 fun l _ => ?_
  rw [v.map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' (hX i l)) (hc l j)

/-- The open-cell condition of level `γ ≤ 1` is preserved by right multiplication by a matrix
congruent to `1` modulo `γ`. -/
theorem InCell.mul_right {γ : Γ₀} (hγ0 : γ ≠ 0) (hγ1 : γ ≤ 1)
    {g k : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K}
    (hk : ∀ a b, v (k a b - (1 : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K) a b) < γ)
    (hg : InCell v r t γ g) : InCell v r t γ (g * k) := by
  obtain ⟨hA, hc⟩ := hg
  have hk1 : ∀ a b, v (k a b) ≤ 1 := by
    intro a b
    have e : k a b = (k a b - (1 : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K) a b) +
        (1 : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K) a b := by ring
    rw [e]
    refine le_trans (v.map_add _ _) (max_le (le_trans (hk a b).le hγ1) ?_)
    rw [Matrix.one_apply]
    split_ifs
    · rw [v.map_one]
    · rw [v.map_zero]
      exact zero_le_one' Γ₀
  set A := botLeft r t g with hAdef
  set c := cellCoord r t g with hcdef
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hB : botRight r t g = A * c := by
    rw [hcdef, cellCoord, ← hAdef, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hAu,
      Matrix.one_mul]
  set M := kLL r t k + c * kRL r t k with hMdef
  set N := kLR r t k + c * kRR r t k with hNdef
  have hL : botLeft r t (g * k) = A * M := by
    rw [botLeft_mul, hB, Matrix.mul_assoc, ← Matrix.mul_add]
  have hR : botRight r t (g * k) = A * N := by
    rw [botRight_mul, hB, Matrix.mul_assoc, ← Matrix.mul_add]
  have hM : ∀ i j, v (M i j - (1 : Matrix (Fin (t + 1)) (Fin (t + 1)) K) i j) < γ := by
    intro i j
    have e : M i j - (1 : Matrix (Fin (t + 1)) (Fin (t + 1)) K) i j =
        (k (leftIdx r t i) (leftIdx r t j) -
          (1 : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K) (leftIdx r t i) (leftIdx r t j)) +
        (c * kRL r t k) i j := by
      rw [hMdef, Matrix.add_apply, Matrix.one_apply, Matrix.one_apply]
      simp only [kLL, (leftIdx_injective r t).eq_iff]
      ring
    rw [e]
    exact v.map_add_lt (hk _ _) (map_mul_lt_of_lt hγ0 hc (fun a b => hk1 _ _) i j)
  have hN : ∀ i j, v (N i j) < γ := by
    intro i j
    have e : N i j = (k (leftIdx r t i) (rightIdx r t j) -
          (1 : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K) (leftIdx r t i) (rightIdx r t j)) +
        (c * kRR r t k) i j := by
      rw [hNdef, Matrix.add_apply, Matrix.one_apply_ne (leftIdx_ne_rightIdx r t i j)]
      simp only [kLR]
      ring
    rw [e]
    exact v.map_add_lt (hk _ _) (map_mul_lt_of_lt hγ0 hc (fun a b => hk1 _ _) i j)
  obtain ⟨hMdet, hMinv⟩ := det_and_inv_of_close_one hγ0 hγ1 hM
  have hMdet0 : M.det ≠ 0 := by
    intro h
    rw [h, v.map_zero] at hMdet
    exact zero_ne_one hMdet
  refine ⟨?_, fun i j => ?_⟩
  · rw [hL, Matrix.det_mul]
    exact mul_ne_zero hA hMdet0
  · have e : cellCoord r t (g * k) = M⁻¹ * N := by
      rw [cellCoord, hL, hR, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc A⁻¹,
        Matrix.nonsing_inv_mul _ hAu, Matrix.one_mul]
    rw [e]
    exact map_mul_lt_of_lt' hγ0 hMinv hN i j

end Valuation

section OpenCell

variable {K : Type*} [Field K] {r t : ℕ}

/-- The matrix `w u'(y)` of size `r + t + 2`, for Shahidi's block Weyl representative `w` and the
matrix `u'(y)` of the exchanged upper radical. -/
abbrev openCellMatrix (y : Matrix (Fin (t + 1)) (Fin (r + 1)) K) :
    Matrix.GeneralLinearGroup (Fin (r + t + 2)) K :=
  GeneralLinear.reindex (finCongr (show r + 1 + (t + 1) = r + t + 2 by omega))
    (Shahidi.blockWeyl (r + 1) (t + 1) K * Shahidi.intertwiningUnipotent (r + 1) (t + 1) K y)

theorem openCellMatrix_bot (y : Matrix (Fin (t + 1)) (Fin (r + 1)) K) (i : Fin (t + 1))
    (c : Fin (r + t + 2)) :
    (openCellMatrix y : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K) (botIdx r t i) c =
      (Shahidi.upper (t + 1) (r + 1) K y : Matrix (Fin (t + 1 + (r + 1))) (Fin (t + 1 + (r + 1))) K)
        (Fin.castAdd (r + 1) i) (Fin.cast (by omega) c) := by
  change ((Shahidi.blockWeyl (r + 1) (t + 1) K : Matrix (Fin (r + 1 + (t + 1)))
      (Fin (r + 1 + (t + 1))) K) * (Shahidi.intertwiningUnipotent (r + 1) (t + 1) K y :
        Matrix (Fin (r + 1 + (t + 1))) (Fin (r + 1 + (t + 1))) K))
      (Fin.natAdd (r + 1) i) (Fin.cast (by omega) c) = _
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.cast (Nat.add_comm (t + 1) (r + 1))
    (Fin.castAdd (r + 1) i))]
  · rw [Shahidi.blockWeyl_entry, Shahidi.blockWeylPermutation_first]
    simp only [↓reduceIte, one_mul]
    rfl
  · intro l _ hl
    rw [Shahidi.blockWeyl_entry]
    split_ifs with h
    · exfalso
      apply hl
      apply (Shahidi.blockWeylPermutation (r + 1) (t + 1)).injective
      rw [h, Shahidi.blockWeylPermutation_first]
    · rw [zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem botLeft_openCellMatrix (y : Matrix (Fin (t + 1)) (Fin (r + 1)) K) :
    botLeft r t (openCellMatrix y : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K) = 1 := by
  ext i j
  rw [botLeft, openCellMatrix_bot]
  have e : (Fin.cast (by omega) (leftIdx r t j) : Fin (t + 1 + (r + 1))) = Fin.castAdd (r + 1) j :=
    Fin.ext rfl
  rw [e, Shahidi.upper_first_first, Matrix.one_apply]

theorem botRight_openCellMatrix (y : Matrix (Fin (t + 1)) (Fin (r + 1)) K) :
    botRight r t (openCellMatrix y : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K) = y := by
  ext i j
  rw [botRight, openCellMatrix_bot]
  have e : (Fin.cast (by omega) (rightIdx r t j) : Fin (t + 1 + (r + 1))) = Fin.natAdd (t + 1) j :=
    Fin.ext rfl
  rw [e, Shahidi.upper_first_second]

/-- The matrix `w u'(y)` satisfies the open-cell condition of level `γ` exactly when the entries
of `y` have valuation `< γ`. -/
theorem inCell_openCellMatrix_iff {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) (γ : Γ₀) (y : Matrix (Fin (t + 1)) (Fin (r + 1)) K) :
    InCell v r t γ (openCellMatrix y : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) K) ↔
      ∀ i j, v (y i j) < γ := by
  rw [InCell, cellCoord, botLeft_openCellMatrix, botRight_openCellMatrix, Matrix.det_one,
    inv_one, Matrix.one_mul]
  exact and_iff_right one_ne_zero

end OpenCell

end Langlands.Global.CuspidalPairEisenstein.OpenCellCutoff
