import Langlands.Global.RankinSelberg.RealCompactDiracSeed

/-!
# The limiting weight on `O(n)` and its nonzero integral

For `κ ∈ O(n)` with corner minors `Δₗ = corner κ l` (`Δₙ = 1`), `Q = ∏ₗ Δₗ` and the sign part
`P = ∏ₗ (Δₗ Δₗ₊₁)^{p l}`, the weight is

`W(κ) = |P(κ)| Q(κ)^{2m} ∏ₗ |Δₗ(κ)/Δₗ₊₁(κ)|^{s l}`.

Corner minors of orthogonal matrices have absolute value at most `1`, so `|Q| ≤ |Δⱼ|` and,
off `Q = 0`, every ratio `|Δₗ/Δₗ₊₁|` lies in `[|Q|, |Q|⁻¹]`. Hence
`|W| ≤ |Q|^{2m} (|Q|⁻¹)^q` with `q = ∑ₗ |Re s_l|`. Where `|Q|` is close to `1` the product of
ratios is close to `1`, so `Re W` is at least half of the positive function `|P| Q^{2m}`; for
large `m` this region dominates and `Re ∫ W > 0`.
-/

noncomputable section

open Matrix Filter Topology MeasureTheory
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealCompactDirac

open Langlands.Archimedean Langlands.GeneralLinear
open PrincipalSeriesExtension GramFormula RealPrincipalSeriesHilbert OrthogonalFinitePolynomial
open MatrixMinor

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "O" => Matrix.unitaryGroup (Fin n) ℝ

/-! ## Corner minors of orthogonal matrices -/

theorem orthogonal_mul_transpose (κ : O) : (κ : Mat) * (κ : Mat)ᵀ = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.mp κ.2
  rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h

theorem abs_corner_orthogonal_le_one (κ : O) (l : ℕ) : |corner (κ : Mat) l| ≤ 1 :=
  abs_corner_le_one (orthogonal_mul_transpose κ) l

theorem abs_cornerProduct_le_one (κ : O) : |cornerProduct (κ : Mat)| ≤ 1 := by
  rw [cornerProduct, Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun l _ => abs_corner_orthogonal_le_one κ l

theorem abs_cornerProduct_le_corner (κ : O) (j : ℕ) :
    |cornerProduct (κ : Mat)| ≤ |corner (κ : Mat) j| := by
  by_cases hj : j < n
  · rw [cornerProduct, ← Finset.mul_prod_erase Finset.univ (fun l : Fin n => corner (κ : Mat) l)
      (Finset.mem_univ ⟨j, hj⟩), abs_mul]
    have h1 : |∏ l ∈ Finset.univ.erase (⟨j, hj⟩ : Fin n), corner (κ : Mat) l| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
        fun l _ => abs_corner_orthogonal_le_one κ l
    calc |corner (κ : Mat) (⟨j, hj⟩ : Fin n)| *
          |∏ l ∈ Finset.univ.erase (⟨j, hj⟩ : Fin n), corner (κ : Mat) l| ≤
          |corner (κ : Mat) (⟨j, hj⟩ : Fin n)| * 1 :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |corner (κ : Mat) j| := by rw [mul_one]
  · rw [corner_of_le _ (not_lt.1 hj), abs_one]
    exact abs_cornerProduct_le_one κ

theorem abs_signPart_le_one (p : ℕ → ℕ) (κ : O) : |signPart p (κ : Mat)| ≤ 1 := by
  rw [signPart, Finset.abs_prod]
  refine Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun l _ => ?_
  rw [abs_pow, abs_mul]
  exact pow_le_one₀ (by positivity) ((mul_le_mul (abs_corner_orthogonal_le_one κ _)
    (abs_corner_orthogonal_le_one κ _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1))

/-- The total sign exponent `2 ∑ₗ p l`. -/
def signDegree (n : ℕ) (p : ℕ → ℕ) : ℕ := 2 * ∑ l : Fin n, p l

theorem abs_signPart_ge (p : ℕ → ℕ) (κ : O) :
    |cornerProduct (κ : Mat)| ^ signDegree n p ≤ |signPart p (κ : Mat)| := by
  rw [signDegree, pow_mul, ← Finset.prod_pow_eq_pow_sum, signPart, Finset.abs_prod]
  refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun l _ => ?_
  rw [abs_pow, abs_mul, sq]
  exact pow_le_pow_left₀ (by positivity) (mul_le_mul (abs_cornerProduct_le_corner κ _)
    (abs_cornerProduct_le_corner κ _) (abs_nonneg _) (abs_nonneg _)) _

/-- The ratio `|Δₗ/Δₗ₊₁|` of consecutive corner minors. -/
def cornerRatio (X : Mat) (l : ℕ) : ℝ := |corner X l / corner X (l + 1)|

theorem cornerRatio_bounds (κ : O) (hQ : cornerProduct (κ : Mat) ≠ 0) (l : ℕ) :
    |cornerProduct (κ : Mat)| ≤ cornerRatio (κ : Mat) l ∧
      cornerRatio (κ : Mat) l ≤ |cornerProduct (κ : Mat)|⁻¹ := by
  have hQpos : 0 < |cornerProduct (κ : Mat)| := abs_pos.2 hQ
  have h1 := abs_cornerProduct_le_corner κ (l + 1)
  have hpos : 0 < |corner (κ : Mat) (l + 1)| := lt_of_lt_of_le hQpos h1
  have hle1 := abs_corner_orthogonal_le_one κ (l + 1)
  have h0 := abs_cornerProduct_le_corner κ l
  have hle0 := abs_corner_orthogonal_le_one κ l
  unfold cornerRatio
  rw [abs_div]
  constructor
  · rw [le_div_iff₀ hpos]
    calc |cornerProduct (κ : Mat)| * |corner (κ : Mat) (l + 1)| ≤
          |cornerProduct (κ : Mat)| * 1 := mul_le_mul_of_nonneg_left hle1 hQpos.le
      _ ≤ |corner (κ : Mat) l| := by rw [mul_one]; exact h0
  · rw [div_le_iff₀ hpos]
    calc |corner (κ : Mat) l| ≤ 1 := hle0
      _ = |cornerProduct (κ : Mat)|⁻¹ * |cornerProduct (κ : Mat)| := by
          rw [inv_mul_cancel₀ hQpos.ne']
      _ ≤ |cornerProduct (κ : Mat)|⁻¹ * |corner (κ : Mat) (l + 1)| :=
          mul_le_mul_of_nonneg_left h1 (by positivity)

theorem cornerRatio_pos (κ : O) (hQ : cornerProduct (κ : Mat) ≠ 0) (l : ℕ) :
    0 < cornerRatio (κ : Mat) l :=
  lt_of_lt_of_le (abs_pos.2 hQ) (cornerRatio_bounds κ hQ l).1

/-! ## The weight -/

/-- The product `∏ₗ |Δₗ/Δₗ₊₁|^{s l}` of complex powers of the corner ratios. -/
def ratioProduct (s : Fin n → ℂ) (X : Mat) : ℂ :=
  ∏ l : Fin n, ((cornerRatio X l : ℝ) : ℂ) ^ s l

/-- The weight `|P| Q^{2m} ∏ₗ |Δₗ/Δₗ₊₁|^{s l}` on `O(n)`. -/
def weight (p : ℕ → ℕ) (m : ℕ) (s : Fin n → ℂ) (κ : O) : ℂ :=
  ((|signPart p (κ : Mat)| * cornerProduct (κ : Mat) ^ (2 * m) : ℝ) : ℂ) *
    ratioProduct s (κ : Mat)

theorem norm_ratioProduct_le (s : Fin n → ℂ) (κ : O) (hQ : cornerProduct (κ : Mat) ≠ 0) :
    ‖ratioProduct s (κ : Mat)‖ ≤ |cornerProduct (κ : Mat)|⁻¹ ^ growthExponent s := by
  have hQpos : 0 < |cornerProduct (κ : Mat)| := abs_pos.2 hQ
  rw [ratioProduct, norm_prod, growthExponent, Real.rpow_sum_of_pos (inv_pos.2 hQpos)]
  gcongr with l _
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (cornerRatio_pos κ hQ l)]
  obtain ⟨h1, h2⟩ := cornerRatio_bounds κ hQ l
  refine rpow_le_of_le_of_inv_le (cornerRatio_pos κ hQ l) h2 ?_
  exact (inv_le_inv₀ (cornerRatio_pos κ hQ l) hQpos).2 h1

theorem weight_of_cornerProduct_eq_zero (p : ℕ → ℕ) {m : ℕ} (hm : 1 ≤ m) (s : Fin n → ℂ)
    (κ : O) (hQ : cornerProduct (κ : Mat) = 0) : weight p m s κ = 0 := by
  rw [weight, hQ, zero_pow (by omega), mul_zero, Complex.ofReal_zero, zero_mul]

theorem norm_weight_le (p : ℕ → ℕ) {m : ℕ} (hm : 1 ≤ m) (s : Fin n → ℂ) (κ : O) :
    ‖weight p m s κ‖ ≤
      |cornerProduct (κ : Mat)| ^ (2 * m) * |cornerProduct (κ : Mat)|⁻¹ ^ growthExponent s := by
  by_cases hQ : cornerProduct (κ : Mat) = 0
  · rw [weight_of_cornerProduct_eq_zero p hm s κ hQ, norm_zero]
    positivity
  · rw [weight, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_abs, abs_pow]
    calc |signPart p (κ : Mat)| * |cornerProduct (κ : Mat)| ^ (2 * m) *
          ‖ratioProduct s (κ : Mat)‖ ≤
          1 * |cornerProduct (κ : Mat)| ^ (2 * m) *
            |cornerProduct (κ : Mat)|⁻¹ ^ growthExponent s := by
          gcongr
          · exact abs_signPart_le_one p κ
          · exact norm_ratioProduct_le s κ hQ
      _ = _ := by rw [one_mul]

/-- For `0 < x ≤ 1` and `r ≤ k`, `x^k (x⁻¹)^r ≤ 1`. -/
theorem pow_mul_inv_rpow_le_one {x r : ℝ} {k : ℕ} (hx : 0 < x) (hx1 : x ≤ 1) (hr : r ≤ k) :
    x ^ k * x⁻¹ ^ r ≤ 1 := by
  rw [Real.inv_rpow hx.le, ← Real.rpow_natCast, ← Real.rpow_neg hx.le, ← Real.rpow_add hx]
  exact Real.rpow_le_one hx.le hx1 (by linarith)

theorem norm_weight_le_one (p : ℕ → ℕ) {m : ℕ} (hm : 1 ≤ m) (s : Fin n → ℂ)
    (hq : growthExponent s ≤ 2 * m) (κ : O) : ‖weight p m s κ‖ ≤ 1 := by
  by_cases hQ : cornerProduct (κ : Mat) = 0
  · rw [weight_of_cornerProduct_eq_zero p hm s κ hQ, norm_zero]
    exact zero_le_one
  · refine (norm_weight_le p hm s κ).trans ?_
    exact pow_mul_inv_rpow_le_one (abs_pos.2 hQ) (abs_cornerProduct_le_one κ)
      (by exact_mod_cast hq)

theorem continuous_corner (l : ℕ) : Continuous fun X : Mat => corner X l :=
  continuous_minor (tail n l) (tail n l)

theorem continuous_cornerProduct : Continuous (cornerProduct (n := n)) := by
  unfold cornerProduct
  exact continuous_finsetProd _ fun l _ => continuous_corner l

theorem measurable_weight (p : ℕ → ℕ) (m : ℕ) (s : Fin n → ℂ) :
    Measurable (weight (n := n) p m s) := by
  have hc : ∀ l : ℕ, Continuous fun κ : O => corner (κ : Mat) l := fun l =>
    (continuous_corner l).comp continuous_subtype_val
  have hsign : Continuous fun κ : O => signPart p (κ : Mat) := by
    unfold signPart
    fun_prop
  have hprod : Continuous fun κ : O => cornerProduct (κ : Mat) :=
    continuous_cornerProduct.comp continuous_subtype_val
  have hratio : ∀ l : Fin n, Measurable fun κ : O => cornerRatio (κ : Mat) l := by
    intro l
    unfold cornerRatio
    exact continuous_abs.measurable.comp ((hc l).measurable.div (hc ((l : ℕ) + 1)).measurable)
  unfold weight ratioProduct
  refine Measurable.mul ?_ (Finset.measurable_prod _ fun l _ => ?_)
  · exact Complex.measurable_ofReal.comp ((hsign.abs.mul (hprod.pow _)).measurable)
  · exact (Complex.measurable_ofReal.comp (hratio l)).pow_const _

theorem integrable_weight (p : ℕ → ℕ) {m : ℕ} (hm : 1 ≤ m) (s : Fin n → ℂ)
    (hq : growthExponent s ≤ 2 * m) : Integrable (weight (n := n) p m s) (haarOrthogonal n) :=
  (integrable_const (1 : ℝ)).mono' (measurable_weight p m s).aestronglyMeasurable
    (Eventually.of_forall fun κ => norm_weight_le_one p hm s hq κ)

/-! ## The product of ratios near the maximum of `|Q|` -/

/-- The sum `∑ₗ ‖s l‖`. -/
def exponentNorm (s : Fin n → ℂ) : ℝ := ∑ l, ‖s l‖

theorem exponentNorm_nonneg (s : Fin n → ℂ) : 0 ≤ exponentNorm s :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- The threshold `exp(-1/(4 ∑ ‖s l‖ + 4))` for `|Q|`. -/
def laplaceThreshold (s : Fin n → ℂ) : ℝ := Real.exp (-(1 / (4 * exponentNorm s + 4)))

theorem laplaceThreshold_pos (s : Fin n → ℂ) : 0 < laplaceThreshold s := Real.exp_pos _

theorem laplaceThreshold_lt_one (s : Fin n → ℂ) : laplaceThreshold s < 1 := by
  have h0 := exponentNorm_nonneg s
  have h1 : 0 < 1 / (4 * exponentNorm s + 4) := by positivity
  calc laplaceThreshold s < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
    _ = 1 := Real.exp_zero

theorem re_ratioProduct_ge (s : Fin n → ℂ) (κ : O)
    (hQ : laplaceThreshold s < |cornerProduct (κ : Mat)|) :
    1 / 2 ≤ (ratioProduct s (κ : Mat)).re := by
  have hQpos : 0 < |cornerProduct (κ : Mat)| := (laplaceThreshold_pos s).trans hQ
  have hQ0 : cornerProduct (κ : Mat) ≠ 0 := abs_pos.1 hQpos
  set S := exponentNorm s with hS
  have hS0 : 0 ≤ S := exponentNorm_nonneg s
  set z : ℂ := ∑ l : Fin n, ((Real.log (cornerRatio (κ : Mat) l) : ℝ) : ℂ) * s l with hz
  have hprod : ratioProduct s (κ : Mat) = Complex.exp z := by
    rw [ratioProduct, hz, Complex.exp_sum]
    refine Finset.prod_congr rfl fun l _ => ?_
    have hpos := cornerRatio_pos κ hQ0 l
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le]
  have hlogQ : -Real.log |cornerProduct (κ : Mat)| < 1 / (4 * S + 4) := by
    have h := Real.log_lt_log (laplaceThreshold_pos s) hQ
    rw [laplaceThreshold, Real.log_exp] at h
    linarith
  have hlog : ∀ l : Fin n, |Real.log (cornerRatio (κ : Mat) l)| ≤
      -Real.log |cornerProduct (κ : Mat)| := by
    intro l
    obtain ⟨h1, h2⟩ := cornerRatio_bounds κ hQ0 l
    have hpos := cornerRatio_pos κ hQ0 l
    rw [abs_le]
    constructor
    · have := Real.log_le_log hQpos h1
      linarith
    · have := Real.log_le_log hpos h2
      rwa [Real.log_inv] at this
  have hnz : ‖z‖ ≤ 1 / 4 := by
    calc ‖z‖ ≤ ∑ l : Fin n, ‖((Real.log (cornerRatio (κ : Mat) l) : ℝ) : ℂ) * s l‖ :=
          norm_sum_le _ _
      _ ≤ ∑ l : Fin n, -Real.log |cornerProduct (κ : Mat)| * ‖s l‖ := by
          gcongr with l
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hlog l) (norm_nonneg _)
      _ = -Real.log |cornerProduct (κ : Mat)| * S := by rw [← Finset.mul_sum]; rfl
      _ ≤ 1 / (4 * S + 4) * S := by
          apply mul_le_mul_of_nonneg_right hlogQ.le hS0
      _ ≤ 1 / 4 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith
  have hexp := Complex.norm_exp_sub_one_le (x := z) (by linarith)
  have hre : -(Complex.exp z - 1).re ≤ ‖Complex.exp z - 1‖ :=
    (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  rw [hprod]
  have : (Complex.exp z).re = 1 + (Complex.exp z - 1).re := by simp
  rw [this]
  linarith

/-! ## Laplace's argument -/

/-- **Nonvanishing of the integral of the weight.** For all sufficiently large `m`,
`Re ∫_{O(n)} W > 0`. -/
theorem exists_re_integral_weight_pos (p : ℕ → ℕ) (s : Fin n → ℂ) :
    ∃ M₀ : ℕ, ∀ m, M₀ ≤ m →
      0 < (∫ κ, weight p m s κ ∂haarOrthogonal n).re := by
  set μ := haarOrthogonal n
  set q := growthExponent s with hq
  set Q₀ := laplaceThreshold s with hQ₀
  have hQ₀pos : 0 < Q₀ := laplaceThreshold_pos s
  have hQ₀1 : Q₀ < 1 := laplaceThreshold_lt_one s
  set Q₁ := (1 + Q₀) / 2 with hQ₁
  have hQ₁gt : Q₀ < Q₁ := by rw [hQ₁]; linarith
  have hQ₁1 : Q₁ < 1 := by rw [hQ₁]; linarith
  have hQ₁pos : 0 < Q₁ := hQ₀pos.trans hQ₁gt
  set A₁ : Set O := {κ | Q₁ < |cornerProduct (κ : Mat)|} with hA₁
  have hA₁open : IsOpen A₁ :=
    isOpen_lt continuous_const ((continuous_cornerProduct.comp continuous_subtype_val).abs)
  have h1A : (1 : O) ∈ A₁ := by
    have : cornerProduct ((1 : O) : Mat) = 1 := by
      rw [cornerProduct]
      refine Finset.prod_eq_one fun l _ => ?_
      rw [corner]
      simp [minor_one]
    simp only [hA₁, Set.mem_ofPred_eq, this, abs_one]
    exact hQ₁1
  have hμA : 0 < μ.real A₁ := by
    have hpos : 0 < μ A₁ := hA₁open.measure_pos μ ⟨1, h1A⟩
    exact ENNReal.toReal_pos hpos.ne' (measure_ne_top μ A₁)
  set d := signDegree n p
  set c := 1 / 2 * Q₁ ^ d * Q₀ ^ q * μ.real A₁ with hc
  have hcpos : 0 < c := by positivity
  have hr : (Q₀ / Q₁) ^ 2 < 1 := by
    have h0 : 0 < Q₀ / Q₁ := div_pos hQ₀pos hQ₁pos
    have h1 : Q₀ / Q₁ < 1 := (div_lt_one hQ₁pos).2 hQ₁gt
    nlinarith
  obtain ⟨Md, hMd⟩ := exists_pow_lt_of_lt_one hcpos hr
  refine ⟨max (max Md 1) ⌈q⌉₊, fun m hm => ?_⟩
  have hmMd : Md ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm1 : 1 ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hmq : q ≤ 2 * m := by
    have h1 : q ≤ ⌈q⌉₊ := Nat.le_ceil q
    have h2 : (⌈q⌉₊ : ℝ) ≤ m := by exact_mod_cast le_trans (le_max_right _ _) hm
    have h3 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  set c₁ := 1 / 2 * Q₁ ^ (d + 2 * m) with hc₁
  set c₂ := Q₀ ^ (2 * m) * Q₀⁻¹ ^ q with hc₂
  have hc₂nn : 0 ≤ c₂ := by positivity
  -- the pointwise lower bound
  have hpt : ∀ κ : O, c₁ * A₁.indicator (fun _ => (1 : ℝ)) κ - c₂ ≤ (weight p m s κ).re := by
    intro κ
    by_cases hQ : cornerProduct (κ : Mat) = 0
    · have hnot : κ ∉ A₁ := by
        simp only [hA₁, Set.mem_ofPred_eq, hQ, abs_zero, not_lt]
        exact hQ₁pos.le
      rw [Set.indicator_of_notMem hnot, weight_of_cornerProduct_eq_zero p hm1 s κ hQ]
      simp only [mul_zero, zero_sub, Complex.zero_re, neg_nonpos]
      exact hc₂nn
    · have hQpos : 0 < |cornerProduct (κ : Mat)| := abs_pos.2 hQ
      by_cases hsmall : |cornerProduct (κ : Mat)| ≤ Q₀
      · have hnot : κ ∉ A₁ := by
          simp only [hA₁, Set.mem_ofPred_eq, not_lt]
          linarith
        rw [Set.indicator_of_notMem hnot, mul_zero, zero_sub]
        have hW := norm_weight_le p hm1 s κ
        have hmono : |cornerProduct (κ : Mat)| ^ (2 * m) *
            |cornerProduct (κ : Mat)|⁻¹ ^ q ≤ c₂ := by
          rw [hc₂, Real.inv_rpow hQpos.le, Real.inv_rpow hQ₀pos.le, ← div_eq_mul_inv,
            ← div_eq_mul_inv, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_sub hQpos,
            ← Real.rpow_sub hQ₀pos]
          exact Real.rpow_le_rpow hQpos.le hsmall (by push_cast; linarith)
        have := (Complex.abs_re_le_norm (weight p m s κ))
        have h2 := neg_abs_le (weight p m s κ).re
        linarith
      · push Not at hsmall
        have hreΦ := re_ratioProduct_ge s κ hsmall
        have hrew : (weight p m s κ).re = (|signPart p (κ : Mat)| *
            cornerProduct (κ : Mat) ^ (2 * m)) * (ratioProduct s (κ : Mat)).re := by
          rw [weight, Complex.re_ofReal_mul]
        have hnn : 0 ≤ |signPart p (κ : Mat)| * cornerProduct (κ : Mat) ^ (2 * m) := by
          have : 0 ≤ cornerProduct (κ : Mat) ^ (2 * m) := by
            rw [pow_mul]; positivity
          positivity
        have hlow : 1 / 2 * (|signPart p (κ : Mat)| * cornerProduct (κ : Mat) ^ (2 * m)) ≤
            (weight p m s κ).re := by
          rw [hrew, mul_comm (1 / 2 : ℝ)]
          exact mul_le_mul_of_nonneg_left hreΦ hnn
        by_cases hin : κ ∈ A₁
        · simp only [Set.indicator_of_mem hin, mul_one]
          have hin' : Q₁ < |cornerProduct (κ : Mat)| := hin
          have hQ2 : cornerProduct (κ : Mat) ^ (2 * m) = |cornerProduct (κ : Mat)| ^ (2 * m) :=
            (Even.pow_abs ⟨m, by ring⟩ _).symm
          have h3 : Q₁ ^ (d + 2 * m) ≤ |signPart p (κ : Mat)| *
              cornerProduct (κ : Mat) ^ (2 * m) := by
            rw [pow_add, hQ2]
            exact mul_le_mul (le_trans (pow_le_pow_left₀ hQ₁pos.le hin'.le d)
              (abs_signPart_ge p κ)) (pow_le_pow_left₀ hQ₁pos.le hin'.le _) (by positivity)
              (abs_nonneg _)
          have : c₁ ≤ 1 / 2 * (|signPart p (κ : Mat)| * cornerProduct (κ : Mat) ^ (2 * m)) := by
            rw [hc₁]
            linarith
          linarith
        · rw [Set.indicator_of_notMem hin, mul_zero, zero_sub]
          have : 0 ≤ 1 / 2 * (|signPart p (κ : Mat)| * cornerProduct (κ : Mat) ^ (2 * m)) := by
            positivity
          linarith
  have hWint := integrable_weight p hm1 s hmq
  have hre_int : Integrable (fun κ => (weight p m s κ).re) μ := hWint.re
  have hind : Integrable (fun κ => c₁ * A₁.indicator (fun _ => (1 : ℝ)) κ - c₂) μ :=
    (((integrable_const (1 : ℝ)).indicator hA₁open.measurableSet).const_mul c₁).sub
      (integrable_const c₂)
  have hmono := integral_mono hind hre_int hpt
  have hcalc : ∫ κ, (c₁ * A₁.indicator (fun _ => (1 : ℝ)) κ - c₂) ∂μ = c₁ * μ.real A₁ - c₂ := by
    rw [integral_sub ((integrable_const (1 : ℝ)).indicator hA₁open.measurableSet |>.const_mul c₁)
      (integrable_const c₂), integral_const_mul, integral_indicator_const (1 : ℝ) hA₁open.measurableSet,
      integral_const]
    simp [μ]
  have hre : ∫ κ, (weight p m s κ).re ∂μ = (∫ κ, weight p m s κ ∂μ).re := integral_re hWint
  have hinv : Q₀ ^ q * Q₀⁻¹ ^ q = 1 := by
    rw [← Real.mul_rpow hQ₀pos.le (inv_nonneg.2 hQ₀pos.le), mul_inv_cancel₀ hQ₀pos.ne',
      Real.one_rpow]
  have hrm : ((Q₀ / Q₁) ^ 2) ^ m < c :=
    lt_of_le_of_lt (pow_le_pow_of_le_one (by positivity) hr.le hmMd) hMd
  have hkey : c₂ < c₁ * μ.real A₁ := by
    have hQ₁m : 0 < Q₁ ^ (2 * m) := by positivity
    have hinvq : 0 < Q₀⁻¹ ^ q := Real.rpow_pos_of_pos (inv_pos.2 hQ₀pos) _
    calc c₂ = ((Q₀ / Q₁) ^ 2) ^ m * Q₁ ^ (2 * m) * Q₀⁻¹ ^ q := by
          rw [hc₂, div_pow, div_pow, ← pow_mul, ← pow_mul, div_mul_cancel₀ _ (by positivity)]
      _ < c * Q₁ ^ (2 * m) * Q₀⁻¹ ^ q := by gcongr
      _ = 1 / 2 * Q₁ ^ d * (Q₀ ^ q * Q₀⁻¹ ^ q) * μ.real A₁ * Q₁ ^ (2 * m) := by
          rw [hc]
          ring
      _ = c₁ * μ.real A₁ := by
          rw [hinv, hc₁, pow_add]
          ring
  rw [← hre]
  linarith

end Langlands.Global.RankinSelbergGlobal.RealCompactDirac
