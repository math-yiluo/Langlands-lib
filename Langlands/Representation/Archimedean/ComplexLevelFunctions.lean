import Langlands.Representation.Archimedean.ComplexDuality.GramWeight

/-!
# Level functions on `GL_n(ℂ)`: determinants and Gram determinants of the lower rows

For `m ≤ n` and a matrix `A` with `n` rows and columns indexed by the rows `m, …, n-1`,
`levelDet m A y = det (Y_m A)` where `Y_m` is the matrix of the rows `m, …, n-1` of `y`.
Under left multiplication by an upper triangular `b` it is multiplied by
`∏_{k ≥ m} b_kk` (`levelDet_upper_mul`), and right multiplication by `x` replaces `A` by
`x A` (`levelDet_mul`).

`levelChar m h b dτ a` is the character `|c|^{2 dτ - h - b} c^h c̄^b`, `c = ∏_{k ≥ m} a_k`, of a
level with `h` holomorphic and `b` antiholomorphic determinant factors; `prod_levelChar` is the
telescoping identity expressing the product of the level characters as
`∏_k phase(a_k)^{l_k} |a_k|^{2 τ_k}` when the level data add up to `l` and `τ`.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator ComplexConjugate ContDiff

set_option autoImplicit false

namespace Langlands.Archimedean.LevelFunctions

open Langlands.Archimedean.ComplexDuality Langlands.GeneralLinear

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

/-- The rows `m, …, n-1` as an index type. -/
abbrev Tail (n m : ℕ) := {j : Fin n // m ≤ (j : ℕ)}

/-- `det (Y_m A)`, `Y_m` the rows `m, …, n-1` of `y`. -/
def levelDet (m : ℕ) (A : Matrix (Fin n) (Tail n m) ℂ) (y : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (tailRows m y * A).det

theorem levelDet_mul (m : ℕ) (A : Matrix (Fin n) (Tail n m) ℂ) (y x : Matrix (Fin n) (Fin n) ℂ) :
    levelDet m A (y * x) = levelDet m (x * A) y := by
  rw [levelDet, levelDet, tailRows_mul, Matrix.mul_assoc]

theorem levelDet_upper_mul (m : ℕ) (A : Matrix (Fin n) (Tail n m) ℂ)
    {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsUpperTriangular) (y : Matrix (Fin n) (Fin n) ℂ) :
    levelDet m A (b * y) = (∏ i : Tail n m, b i i) * levelDet m A y := by
  rw [levelDet, levelDet, tailRows_upper_mul m hb, Matrix.mul_assoc, Matrix.det_mul,
    det_submatrix_tail hb]

theorem levelDet_borel_mul (m : ℕ) (A : Matrix (Fin n) (Tail n m) ℂ) (a : Fin n → ℂˣ)
    (u : upperUnipotent n ℂ) (y : Matrix (Fin n) (Fin n) ℂ) :
    levelDet m A ((((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
        (u : Langlands.GeneralLinear n ℂ) : Langlands.GeneralLinear n ℂ) :
          Matrix (Fin n) (Fin n) ℂ) * y) =
      (∏ i : Tail n m, (a i : ℂ)) * levelDet m A y := by
  have hb : (Matrix.diagonal (fun i => (a i : ℂ)) *
      ((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)).IsUpperTriangular :=
    (Matrix.blockTriangular_diagonal _).mul u.2.1
  rw [val_diagonalUnits_mul, levelDet_upper_mul m A hb]
  congr 2
  funext i
  rw [Matrix.diagonal_mul, u.2.2 i, mul_one]

/-- The selection of the columns `m, …, n-1`: `levelDet m (tailSelect m) 1 = 1`. -/
def tailSelect (m : ℕ) : Matrix (Fin n) (Tail n m) ℂ :=
  Matrix.of fun j i => if j = (i : Fin n) then 1 else 0

theorem levelDet_tailSelect_one (m : ℕ) :
    levelDet m (tailSelect m) (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  have : tailRows m (1 : Matrix (Fin n) (Fin n) ℂ) * tailSelect m =
      (1 : Matrix (Tail n m) (Tail n m) ℂ) := by
    ext i i'
    simp only [tailRows, tailSelect, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (i : Fin n)]
    · simp [Subtype.ext_iff]
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  rw [levelDet, this, Matrix.det_one]

theorem contDiff_levelDet (m : ℕ) (A : Matrix (Fin n) (Tail n m) ℂ) :
    ContDiff ℝ ∞ (levelDet m A : Matrix (Fin n) (Fin n) ℂ → ℂ) := by
  have hentry : ∀ i j : Fin n,
      ContDiff ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℂ => y i j) := by
    intro i j
    let e : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
      { toFun := fun y => y i j
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact (LinearMap.toContinuousLinearMap e).contDiff
  have hM : ∀ i i' : Tail n m,
      ContDiff ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℂ => (tailRows m y * A) i i') := by
    intro i i'
    simp only [Matrix.mul_apply, tailRows, Matrix.of_apply]
    exact ContDiff.sum fun k _ => (hentry i k).mul contDiff_const
  unfold levelDet
  simp_rw [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hM (σ i) i)

/-! ## The telescoping character identity -/

/-- The phase `z / |z|` of a nonzero complex number. -/
def phase (z : ℂˣ) : ℂ := (z : ℂ) / (‖(z : ℂ)‖ : ℂ)

theorem phase_ne_zero (z : ℂˣ) : phase z ≠ 0 := by
  unfold phase
  exact div_ne_zero z.ne_zero (by exact_mod_cast norm_ne_zero_iff.2 z.ne_zero)

theorem conj_phase (z : ℂˣ) : conj (phase z) = (phase z)⁻¹ := by
  have hn : (‖(z : ℂ)‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 z.ne_zero
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  unfold phase
  rw [map_div₀, Complex.conj_ofReal, inv_div]
  field_simp
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem eq_phase_mul_norm (z : ℂˣ) : (z : ℂ) = phase z * (‖(z : ℂ)‖ : ℂ) := by
  have hn : (‖(z : ℂ)‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 z.ne_zero
  unfold phase
  rw [div_mul_cancel₀ _ hn]

theorem prod_cpow_ofReal_nonneg {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    (r : ℂ) : ((∏ i ∈ s, x i : ℝ) : ℂ) ^ r = ∏ i ∈ s, ((x i : ℝ) : ℂ) ^ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hx i) (Finset.prod_nonneg fun j _ => hx j), ih]

theorem norm_pow_eq_cpow (z : ℂˣ) (N : ℕ) :
    ((‖(z : ℂ)‖ : ℂ)) ^ N = ((Complex.normSq (z : ℂ) : ℝ) : ℂ) ^ ((N : ℂ) / 2) := by
  have h2 : ((Complex.normSq (z : ℂ) : ℝ) : ℂ) = ((‖(z : ℂ)‖ : ℂ)) ^ (2 : ℕ) := by
    rw [Complex.normSq_eq_norm_sq]; push_cast; ring
  have harg : ((‖(z : ℂ)‖ : ℂ)).arg = 0 := Complex.arg_ofReal_of_nonneg (norm_nonneg _)
  rw [h2, ← Complex.cpow_nat_mul' (by simp [harg, Real.pi_pos]) (by simp [harg, Real.pi_pos.le])]
  rw [show ((2 : ℕ) : ℂ) * ((N : ℂ) / 2) = (N : ℂ) by ring, Complex.cpow_natCast]

theorem norm_cpow_two_mul (z : ℂˣ) (t : ℂ) :
    ((‖(z : ℂ)‖ : ℂ)) ^ (2 * t) = ((Complex.normSq (z : ℂ) : ℝ) : ℂ) ^ t := by
  have h2 : ((Complex.normSq (z : ℂ) : ℝ) : ℂ) = ((‖(z : ℂ)‖ : ℂ)) ^ (2 : ℕ) := by
    rw [Complex.normSq_eq_norm_sq]; push_cast; ring
  have harg : ((‖(z : ℂ)‖ : ℂ)).arg = 0 := Complex.arg_ofReal_of_nonneg (norm_nonneg _)
  rw [h2, ← Complex.cpow_nat_mul' (by simp [harg, Real.pi_pos]) (by simp [harg, Real.pi_pos.le])]
  norm_num

theorem normSq_ne_zero (z : ℂˣ) : ((Complex.normSq (z : ℂ) : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (Complex.normSq_pos.2 z.ne_zero).ne'

/-- The character of one level with `h` holomorphic and `b` antiholomorphic determinant factors:
`|c|^{2 dτ - h - b} c^h c̄^b` for `c = ∏_{k ≥ m} a_k`. -/
def levelChar (m h b : ℕ) (dτ : ℂ) (a : Fin n → ℂˣ) : ℂ :=
  ((∏ i : Tail n m, Complex.normSq (a i : ℂ) : ℝ) : ℂ) ^ (dτ - ((h + b : ℕ) : ℂ) / 2) *
    ((∏ i : Tail n m, (a i : ℂ)) ^ h * conj (∏ i : Tail n m, (a i : ℂ)) ^ b)

theorem levelChar_eq (m h b : ℕ) (dτ : ℂ) (a : Fin n → ℂˣ) :
    levelChar m h b dτ a = ∏ i : Tail n m,
      phase (a i) ^ ((h : ℤ) - b) * ((Complex.normSq (a i : ℂ) : ℝ) : ℂ) ^ dτ := by
  have hmod : ∀ i : Tail n m,
      (‖((a i : ℂˣ) : ℂ)‖ : ℂ) ^ (h + b) * ((Complex.normSq (a i : ℂ) : ℝ) : ℂ) ^
        (dτ - ((h + b : ℕ) : ℂ) / 2) = ((Complex.normSq (a i : ℂ) : ℝ) : ℂ) ^ dτ := by
    intro i
    rw [norm_pow_eq_cpow, ← Complex.cpow_add _ _ (normSq_ne_zero (a i))]
    congr 1
    ring
  unfold levelChar
  rw [prod_cpow_ofReal_nonneg _ _ (fun i => Complex.normSq_nonneg _), map_prod,
    ← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have k1 : ((a i : ℂˣ) : ℂ) ^ h = phase (a i) ^ h * (‖((a i : ℂˣ) : ℂ)‖ : ℂ) ^ h := by
    rw [← mul_pow, ← eq_phase_mul_norm]
  have k2 : conj ((a i : ℂˣ) : ℂ) ^ b =
      ((phase (a i))⁻¹) ^ b * (‖((a i : ℂˣ) : ℂ)‖ : ℂ) ^ b := by
    rw [← mul_pow, ← conj_phase, ← Complex.conj_ofReal, ← map_mul, ← eq_phase_mul_norm]
  rw [k1, k2, ← hmod i, zpow_sub₀ (phase_ne_zero (a i)), zpow_natCast, zpow_natCast, pow_add,
    inv_pow, div_eq_mul_inv]
  ring

theorem prod_zpow_eq_zpow_sum' {ι : Type*} (s : Finset ι) {b : ℂ} (hb : b ≠ 0) (e : ι → ℤ) :
    ∏ i ∈ s, b ^ e i = b ^ ∑ i ∈ s, e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hb]

theorem prod_cpow_eq_cpow_sum {ι : Type*} (s : Finset ι) {x : ℂ} (hx : x ≠ 0) (d : ι → ℂ) :
    ∏ i ∈ s, x ^ d i = x ^ ∑ i ∈ s, d i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih,
      Complex.cpow_add _ _ hx]

theorem prod_tail_comm {M : Type*} [CommMonoid M] (f : ℕ → Fin n → M) :
    ∏ m : Fin n, ∏ i : Tail n m, f m i =
      ∏ i : Fin n, ∏ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ i.val), f m i := by
  have h1 : ∀ m : Fin n, ∏ i : Tail n m, f m i =
      ∏ i : Fin n, if m.val ≤ i.val then f m i else 1 := by
    intro m
    rw [← Finset.prod_filter]
    exact (Finset.prod_subtype (Finset.univ.filter fun i : Fin n => m.val ≤ i.val)
      (fun x => by simp) (fun i => f m i)).symm
  simp_rw [h1, Finset.prod_filter]
  exact Finset.prod_comm

/-- **Telescoping.** If the level exponents add up to the exponents `l k` and `τ k` of the
positions, the product of the level characters is `∏_k phase(a_k)^{l_k} |a_k|^{2 τ_k}`. -/
theorem prod_levelChar (h b : ℕ → ℕ) (dτ : ℕ → ℂ) (l : ℕ → ℤ) (τ : ℕ → ℂ)
    (hl : ∀ k : Fin n, ∑ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val),
      ((h m : ℤ) - b m) = l k)
    (hτ : ∀ k : Fin n, ∑ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val), dτ m = τ k)
    (a : Fin n → ℂˣ) :
    ∏ m : Fin n, levelChar m (h m) (b m) (dτ m) a =
      ∏ k : Fin n, phase (a k) ^ l k * ((Complex.normSq (a k : ℂ) : ℝ) : ℂ) ^ τ k := by
  simp_rw [levelChar_eq]
  rw [prod_tail_comm (fun m i => phase (a i) ^ ((h m : ℤ) - b m) *
    ((Complex.normSq (a i : ℂ) : ℝ) : ℂ) ^ dτ m)]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_mul_distrib, ← hl k, ← hτ k]
  congr 1
  · exact prod_zpow_eq_zpow_sum' _ (phase_ne_zero (a k)) _
  · exact prod_cpow_eq_cpow_sum _ (normSq_ne_zero (a k)) _

end Langlands.Archimedean.LevelFunctions
