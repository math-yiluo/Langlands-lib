import Langlands.Representation.Archimedean.ComplexSwapJacquetChart
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Decay of principal-series vectors along the rank-one chart

Let `ds = pre ++ d :: e :: post`, let `i = pre.length` and `j = i + 1` be the positions of `d`
and `e`, and let `h` lie in the smooth principal series of `ds`. Write `s = t_d - t_e` for the
difference of the exponents and assume `Re s ≥ 0`.

For `z ≠ 0` the chart matrix factors as
`chart z = diag(…, -1/z, z, …) · (1 - z E_ij) · (1 + z⁻¹ E_ji)`
(`chart_eq_mul`), so `h(chart z) = δχ(diag(…, -1/z, z, …)) · h(1 + z⁻¹ E_ji)`, and the
character has absolute value `|z|^(-2 - 2 Re s)` (`norm_principalSeriesCharacter_chartTorus`).
Since `w ↦ h(1 + w E_ji)` is smooth, it is bounded near `0`, and it is `O(|w|)` there when
`h(1) = 0`. Hence

* `|h(chart z)| ≤ C (1 + |z|)⁻¹` for all `z` (`exists_bound_chart`), and
* `|h(chart z)| ≤ C (1 + |z|)⁻³` for all `z` when `h(1) = 0`
  (`exists_bound_chart_of_eq_zero`).
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexSwapJacquet

open Langlands.LocalFactor.Archimedean Langlands.GeneralLinear

variable {n : ℕ}

/-! ## Smoothness along curves in `GL_n(ℂ)` -/

/-- A smooth function on `GL_n(ℂ)` composed with a smooth curve of invertible matrices is
smooth. -/
theorem contDiff_apply_of_val {h : Langlands.GeneralLinear n ℂ → ℂ}
    (hh : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ h) {T : ℂ → Langlands.GeneralLinear n ℂ}
    (hT : ContDiff ℝ ∞ fun w => (T w : Matrix (Fin n) (Fin n) ℂ)) :
    ContDiff ℝ ∞ fun w => h (T w) := by
  have hc := (contDiffOn_unitsExtension hh).comp_contDiff hT fun w => Units.isUnit (T w)
  have hfun : (fun w => h (T w)) =
      unitsExtension h ∘ fun w => (T w : Matrix (Fin n) (Fin n) ℂ) :=
    funext fun w => (unitsExtension_val h (T w)).symm
  rw [hfun]
  exact hc

theorem contDiff_transvection (a b : Fin n) :
    ContDiff ℝ ∞ fun w : ℂ => Matrix.transvection a b w := by
  have hfun : (fun w : ℂ => Matrix.transvection a b w) =
      fun w : ℂ => 1 + w • Matrix.single a b (1 : ℂ) := by
    funext w
    simp [Matrix.transvection, Matrix.smul_single]
  rw [hfun]
  exact contDiff_const.add (contDiff_id.smul contDiff_const)

/-- `z ↦ h(chart z)` is smooth. -/
theorem contDiff_apply_chart {h : Langlands.GeneralLinear n ℂ → ℂ}
    (hh : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ h) (i j : Fin n) (hj : (j : ℕ) = i + 1) :
    ContDiff ℝ ∞ fun z => h (chart i j hj z) :=
  contDiff_apply_of_val hh (contDiff_const.mul (contDiff_transvection i j))

/-- The lower unipotent matrix `1 + w E_ji`. -/
def lowerChart (i j : Fin n) (hj : (j : ℕ) = i + 1) (w : ℂ) : Langlands.GeneralLinear n ℂ :=
  Matrix.GeneralLinearGroup.transvection j i (ne_of_val_eq_succ hj).symm w

theorem lowerChart_zero (i j : Fin n) (hj : (j : ℕ) = i + 1) : lowerChart i j hj 0 = 1 := by
  apply Units.ext
  simp [lowerChart]

/-- `w ↦ h(1 + w E_ji)` is smooth. -/
theorem contDiff_apply_lowerChart {h : Langlands.GeneralLinear n ℂ → ℂ}
    (hh : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ h) (i j : Fin n) (hj : (j : ℕ) = i + 1) :
    ContDiff ℝ ∞ fun w => h (lowerChart i j hj w) :=
  contDiff_apply_of_val hh (contDiff_transvection j i)

/-! ## The factorization of the chart -/

/-- The diagonal `diag(…, -1/z, z, …)`, with `-1/z` at position `i` and `z` at position `j`. -/
def chartTorus (i j : Fin n) (z : ℂˣ) : Fin n → ℂˣ :=
  fun k => if k = i then -z⁻¹ else if k = j then z else 1

/-- The upper unipotent matrix `1 - z E_ij`. -/
def chartUnipotent (i j : Fin n) (hj : (j : ℕ) = i + 1) (z : ℂ) : upperUnipotent n ℂ :=
  ⟨Matrix.GeneralLinearGroup.transvection i j (ne_of_val_eq_succ hj) (-z), by
    refine ⟨fun a b hab => ?_, fun k => ?_⟩
    · change Matrix.transvection i j (-z) a b = 0
      have hab' : a ≠ b := fun h => by rw [h] at hab; exact lt_irrefl _ hab
      have hij : ¬(i = a ∧ j = b) := by
        rintro ⟨rfl, rfl⟩
        have : (j : ℕ) < i := hab
        omega
      simp [Matrix.transvection, hab', hij]
    · change Matrix.transvection i j (-z) k k = 1
      have hij : ¬(i = k ∧ j = k) := by
        rintro ⟨rfl, h⟩
        exact ne_of_val_eq_succ hj h.symm
      simp [Matrix.transvection, hij]⟩

/-- `s x(z) = diag(…, -1/z, z, …) · (1 - z E_ij) · (1 + z⁻¹ E_ji)` for `z ≠ 0`. -/
theorem chart_eq_mul (i j : Fin n) (hj : (j : ℕ) = i + 1) (z : ℂ) (hz : z ≠ 0) :
    chart i j hj z = Iwasawa.diagonalUnits (chartTorus i j (Units.mk0 z hz)) *
      ((chartUnipotent i j hj z : upperUnipotent n ℂ) : Langlands.GeneralLinear n ℂ) *
        lowerChart i j hj z⁻¹ := by
  have hij : i ≠ j := ne_of_val_eq_succ hj
  have hT : ∀ (a b : Fin n) (hab : a ≠ b) (c : ℂ),
      ((Matrix.GeneralLinearGroup.transvection a b hab c : Langlands.GeneralLinear n ℂ) :
        Matrix (Fin n) (Fin n) ℂ) = Matrix.transvection a b c := fun _ _ _ _ => rfl
  apply Units.ext
  simp only [Units.val_mul, chart_val, Iwasawa.diagonalUnits_val, chartUnipotent, lowerChart,
    hT]
  ext a b
  rw [Matrix.mul_assoc, Matrix.diagonal_mul]
  by_cases ha : a = i
  · subst ha
    rw [Matrix.swap_mul_apply_left, Matrix.transvection_mul_apply_same]
    simp only [chartTorus, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply]
    by_cases hb : b = a
    · subst hb
      simp [hij, hij.symm]
      field_simp
      simp
    · by_cases hb' : b = j
      · subst hb'
        simp [hij, hij.symm]
        field_simp
      · simp [hij, Ne.symm hb, Ne.symm hb']
  · by_cases ha' : a = j
    · subst ha'
      rw [Matrix.swap_mul_apply_right, Matrix.transvection_mul_apply_of_ne _ _ _ _ ha]
      simp only [chartTorus, ha, ↓reduceIte, Matrix.transvection, Matrix.add_apply,
        Matrix.one_apply, Matrix.single_apply]
      by_cases hb : b = i
      · subst hb
        simp [hij.symm]
        field_simp
      · by_cases hb' : b = a
        · subst hb'
          simp [hij]
        · simp [Ne.symm hb, Ne.symm hb']
    · rw [Matrix.swap_mul_of_ne ha ha', Matrix.transvection_mul_apply_of_ne _ _ _ _ ha]
      simp only [chartTorus, ha, ha', ↓reduceIte, Matrix.transvection, Matrix.add_apply,
        Matrix.one_apply, Matrix.single_apply]
      simp [Ne.symm ha, Ne.symm ha']

/-- `h(chart z) = δχ(diag(…, -1/z, z, …)) · h(1 + z⁻¹ E_ji)` for `z ≠ 0`. -/
theorem apply_chart_eq {χ : ℕ → ℂˣ → ℂ} {h : Langlands.GeneralLinear n ℂ → ℂ}
    (hh : h ∈ principalSeries ℂ n χ) (i j : Fin n) (hj : (j : ℕ) = i + 1) (z : ℂ)
    (hz : z ≠ 0) :
    h (chart i j hj z) = principalSeriesCharacter ℂ n χ (chartTorus i j (Units.mk0 z hz)) *
      h (lowerChart i j hj z⁻¹) := by
  rw [chart_eq_mul i j hj z hz]
  exact hh.2 _ _ _

/-! ## The absolute value of the character -/

theorem norm_character (d : ComplexCharacterData) (w : ℂˣ) :
    ‖(d.character w : ℂ)‖ = ‖(w : ℂ)‖ ^ (2 * d.exponent.re) := by
  have hw : 0 < ‖(w : ℂ)‖ := norm_pos_iff.mpr w.ne_zero
  rw [d.character_eq, norm_mul, norm_zpow, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hw, div_self hw.ne', one_zpow, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hw]
  simp

theorem complexPositionCharacter_one :
    ∀ (l : List ComplexCharacterData) (p : ℕ), complexPositionCharacter l p 1 = 1
  | [], _ => rfl
  | d :: _, 0 => by simp [complexPositionCharacter]
  | _ :: l, p + 1 => complexPositionCharacter_one l p

theorem complexPositionCharacter_append_length (pre post : List ComplexCharacterData)
    (d e : ComplexCharacterData) :
    complexPositionCharacter (pre ++ d :: e :: post) pre.length =
      fun w => (d.character w : ℂ) := by
  induction pre with
  | nil => rfl
  | cons p pre ih => exact ih

theorem complexPositionCharacter_append_length_succ (pre post : List ComplexCharacterData)
    (d e : ComplexCharacterData) :
    complexPositionCharacter (pre ++ d :: e :: post) (pre.length + 1) =
      fun w => (e.character w : ℂ) := by
  induction pre with
  | nil => rfl
  | cons p pre ih => exact ih

/-- `|δχ(diag(…, -1/z, z, …))| = |z|^(-2 - 2 Re(t_d - t_e))`. -/
theorem norm_principalSeriesCharacter_chartTorus (pre post : List ComplexCharacterData)
    (d e : ComplexCharacterData) (i j : Fin n) (hi : (i : ℕ) = pre.length)
    (hj : (j : ℕ) = i + 1) (z : ℂˣ) :
    ‖principalSeriesCharacter ℂ n (complexPositionCharacter (pre ++ d :: e :: post))
        (chartTorus i j z)‖ =
      ‖(z : ℂ)‖ ^ (-2 - 2 * (d.exponent - e.exponent).re) := by
  have hij : i ≠ j := ne_of_val_eq_succ hj
  have hr : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
  unfold principalSeriesCharacter
  rw [Fintype.prod_eq_mul i j hij]
  · have hti : chartTorus i j z i = -z⁻¹ := by simp [chartTorus]
    have htj : chartTorus i j z j = z := by simp [chartTorus, hij.symm]
    have hχi : complexPositionCharacter (pre ++ d :: e :: post) (i : ℕ) =
        fun w => (d.character w : ℂ) := by
      rw [hi]; exact complexPositionCharacter_append_length pre post d e
    have hχj : complexPositionCharacter (pre ++ d :: e :: post) (j : ℕ) =
        fun w => (e.character w : ℂ) := by
      rw [hj, hi]; exact complexPositionCharacter_append_length_succ pre post d e
    rw [hti, htj, hχi, hχj, norm_mul, norm_mul, norm_mul, norm_character, norm_character,
      Complex.finrank_real_complex]
    have hneg : ‖(((-z⁻¹ : ℂˣ) : ℂ))‖ = ‖(z : ℂ)‖⁻¹ := by
      simp
    rw [hneg, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    have hjR : ((j : ℕ) : ℝ) = ((i : ℕ) : ℝ) + 1 := by rw [hj]; push_cast; ring
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.natCast_re, Complex.one_re]
    rw [hjR]
    rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity),
      Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity),
      Real.rpow_def_of_pos hr, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.log_pow,
      Real.log_pow, Real.log_inv]
    congr 1
    push_cast
    ring
  · rintro k ⟨hki, hkj⟩
    have htk : chartTorus i j z k = 1 := by simp [chartTorus, hki, hkj]
    rw [htk, complexPositionCharacter_one]
    simp

/-- For `|z| ≥ 1` and `Re(t_d - t_e) ≥ 0`: `|δχ(diag(…, -1/z, z, …))| ≤ |z|⁻²`. -/
theorem norm_principalSeriesCharacter_chartTorus_le (pre post : List ComplexCharacterData)
    (d e : ComplexCharacterData) (i j : Fin n) (hi : (i : ℕ) = pre.length)
    (hj : (j : ℕ) = i + 1) (hre : 0 ≤ (d.exponent - e.exponent).re) (z : ℂˣ)
    (hz : 1 ≤ ‖(z : ℂ)‖) :
    ‖principalSeriesCharacter ℂ n (complexPositionCharacter (pre ++ d :: e :: post))
        (chartTorus i j z)‖ ≤ (‖(z : ℂ)‖ ^ 2)⁻¹ := by
  rw [norm_principalSeriesCharacter_chartTorus pre post d e i j hi hj z]
  calc ‖(z : ℂ)‖ ^ (-2 - 2 * (d.exponent - e.exponent).re)
      ≤ ‖(z : ℂ)‖ ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hz (by linarith)
    _ = (‖(z : ℂ)‖ ^ 2)⁻¹ := by
      rw [Real.rpow_neg (by positivity), Real.rpow_two]

/-! ## Elementary bounds -/

theorem exists_bound_ball {ψ : ℂ → ℂ} (hψ : Continuous ψ) :
    ∃ M, 0 ≤ M ∧ ∀ w : ℂ, ‖w‖ ≤ 1 → ‖ψ w‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hψ.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun w hw => (hM w ?_).trans (le_max_left _ _)⟩
  simpa using hw

theorem exists_lipschitz_ball {ψ : ℂ → ℂ} (hψ : ContDiff ℝ 1 ψ) :
    ∃ L, 0 ≤ L ∧ ∀ w : ℂ, ‖w‖ ≤ 1 → ‖ψ w - ψ 0‖ ≤ L * ‖w‖ := by
  obtain ⟨L, hL⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (hψ.continuous_fderiv one_ne_zero).continuousOn
  refine ⟨max L 0, le_max_right _ _, fun w hw => ?_⟩
  have h := (convex_closedBall (0 : ℂ) 1).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => (hψ.differentiable one_ne_zero) x)
    (fun x hx => (hL x hx).trans (le_max_left L 0))
    (Metric.mem_closedBall_self zero_le_one) (by simpa using hw)
  simpa using h

theorem inv_sq_le_two_mul_inv {r : ℝ} (hr : 1 ≤ r) : (r ^ 2)⁻¹ ≤ 2 * (1 + r)⁻¹ := by
  rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem inv_cube_le_eight_mul_inv {r : ℝ} (hr : 1 ≤ r) :
    (r ^ 3)⁻¹ ≤ 8 * ((1 + r) ^ 3)⁻¹ := by
  rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
  have h : 1 + r ≤ 2 * r := by linarith
  have h3 : (1 + r) ^ 3 ≤ (2 * r) ^ 3 := pow_le_pow_left₀ (by positivity) h 3
  nlinarith

theorem one_le_two_mul_inv {r : ℝ} (h0 : 0 ≤ r) (hr : r ≤ 1) : 1 ≤ 2 * (1 + r)⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  linarith

theorem one_le_eight_mul_inv_cube {r : ℝ} (h0 : 0 ≤ r) (hr : r ≤ 1) :
    1 ≤ 8 * ((1 + r) ^ 3)⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have h3 : (1 + r) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
  linarith

/-! ## Decay along the chart -/

/-- For `|z| ≥ 1`: `|h(chart z)| ≤ |z|⁻² |h(1 + z⁻¹ E_ji)|`. -/
theorem norm_apply_chart_le (pre post : List ComplexCharacterData)
    (d e : ComplexCharacterData) (i j : Fin n) (hi : (i : ℕ) = pre.length)
    (hj : (j : ℕ) = i + 1) (hre : 0 ≤ (d.exponent - e.exponent).re)
    {h : Langlands.GeneralLinear n ℂ → ℂ}
    (hh : h ∈ complexStandardModule n (pre ++ d :: e :: post)) (z : ℂ) (hz : 1 ≤ ‖z‖) :
    ‖h (chart i j hj z)‖ ≤ (‖z‖ ^ 2)⁻¹ * ‖h (lowerChart i j hj z⁻¹)‖ := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
    linarith
  rw [apply_chart_eq hh i j hj z hz0, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (norm_principalSeriesCharacter_chartTorus_le pre post d e i j hi hj hre (Units.mk0 z hz0)
      (by simpa using hz)) (norm_nonneg _)

/-- **Decay.** `|h(chart z)| ≤ C (1 + |z|)⁻¹` when `Re(t_d - t_e) ≥ 0`. -/
theorem exists_bound_chart (pre post : List ComplexCharacterData)
    (d e : ComplexCharacterData) (i j : Fin n) (hi : (i : ℕ) = pre.length)
    (hj : (j : ℕ) = i + 1) (hre : 0 ≤ (d.exponent - e.exponent).re)
    {h : Langlands.GeneralLinear n ℂ → ℂ}
    (hh : h ∈ complexStandardModule n (pre ++ d :: e :: post)) :
    ∃ C, ∀ z, ‖h (chart i j hj z)‖ ≤ C * (1 + ‖z‖)⁻¹ := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_ball (contDiff_apply_lowerChart hh.1 i j hj).continuous
  obtain ⟨M', hM'0, hM'⟩ := exists_bound_ball (contDiff_apply_chart hh.1 i j hj).continuous
  refine ⟨2 * (M + M'), fun z => ?_⟩
  rcases le_total ‖z‖ 1 with hz | hz
  · have h1 := one_le_two_mul_inv (norm_nonneg z) hz
    calc ‖h (chart i j hj z)‖ ≤ M' := hM' z hz
      _ ≤ (M + M') * (2 * (1 + ‖z‖)⁻¹) := by nlinarith
      _ = 2 * (M + M') * (1 + ‖z‖)⁻¹ := by ring
  · have hw : ‖z⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ hz
    have h1 := inv_sq_le_two_mul_inv hz
    calc ‖h (chart i j hj z)‖ ≤ (‖z‖ ^ 2)⁻¹ * ‖h (lowerChart i j hj z⁻¹)‖ :=
          norm_apply_chart_le pre post d e i j hi hj hre hh z hz
      _ ≤ (2 * (1 + ‖z‖)⁻¹) * (M + M') := by
          have := hM z⁻¹ hw
          have h0 : 0 ≤ (‖z‖ ^ 2)⁻¹ := by positivity
          nlinarith [norm_nonneg (h (lowerChart i j hj z⁻¹))]
      _ = 2 * (M + M') * (1 + ‖z‖)⁻¹ := by ring

/-- **Decay, vanishing at `1`.** `|h(chart z)| ≤ C (1 + |z|)⁻³` when `Re(t_d - t_e) ≥ 0` and
`h(1) = 0`. -/
theorem exists_bound_chart_of_eq_zero (pre post : List ComplexCharacterData)
    (d e : ComplexCharacterData) (i j : Fin n) (hi : (i : ℕ) = pre.length)
    (hj : (j : ℕ) = i + 1) (hre : 0 ≤ (d.exponent - e.exponent).re)
    {h : Langlands.GeneralLinear n ℂ → ℂ}
    (hh : h ∈ complexStandardModule n (pre ++ d :: e :: post)) (h1 : h 1 = 0) :
    ∃ C, ∀ z, ‖h (chart i j hj z)‖ ≤ C * ((1 + ‖z‖) ^ 3)⁻¹ := by
  obtain ⟨L, hL0, hL⟩ := exists_lipschitz_ball
    ((contDiff_apply_lowerChart hh.1 i j hj).of_le (by exact_mod_cast le_top))
  obtain ⟨M', hM'0, hM'⟩ := exists_bound_ball (contDiff_apply_chart hh.1 i j hj).continuous
  have hψ0 : h (lowerChart i j hj 0) = 0 := by rw [lowerChart_zero, h1]
  refine ⟨8 * (L + M'), fun z => ?_⟩
  rcases le_total ‖z‖ 1 with hz | hz
  · have h8 := one_le_eight_mul_inv_cube (norm_nonneg z) hz
    calc ‖h (chart i j hj z)‖ ≤ M' := hM' z hz
      _ ≤ (L + M') * (8 * ((1 + ‖z‖) ^ 3)⁻¹) := by nlinarith
      _ = 8 * (L + M') * ((1 + ‖z‖) ^ 3)⁻¹ := by ring
  · have hw : ‖z⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ hz
    have hLw := hL z⁻¹ hw
    rw [hψ0, sub_zero, norm_inv] at hLw
    have h8 := inv_cube_le_eight_mul_inv hz
    have hpos : 0 < ‖z‖ := by linarith
    have hcube : (‖z‖ ^ 2)⁻¹ * ‖z‖⁻¹ = (‖z‖ ^ 3)⁻¹ := by
      field_simp
    calc ‖h (chart i j hj z)‖ ≤ (‖z‖ ^ 2)⁻¹ * ‖h (lowerChart i j hj z⁻¹)‖ :=
          norm_apply_chart_le pre post d e i j hi hj hre hh z hz
      _ ≤ (‖z‖ ^ 2)⁻¹ * (L * ‖z‖⁻¹) :=
          mul_le_mul_of_nonneg_left hLw (by positivity)
      _ = L * (‖z‖ ^ 3)⁻¹ := by rw [← hcube]; ring
      _ ≤ L * (8 * ((1 + ‖z‖) ^ 3)⁻¹) := mul_le_mul_of_nonneg_left h8 hL0
      _ ≤ 8 * (L + M') * ((1 + ‖z‖) ^ 3)⁻¹ := by
          have : 0 ≤ ((1 + ‖z‖) ^ 3)⁻¹ := by positivity
          nlinarith

end Langlands.Archimedean.ComplexSwapJacquet
