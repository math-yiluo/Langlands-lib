import Langlands.Global.RankinSelberg.RealWhittakerGauge
import Langlands.Global.RankinSelberg.RealIwasawaMeasure
import Langlands.Global.RankinSelberg.RealConvergenceAnalysis
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! # Convergence and holomorphy of the real equal-rank Rankin–Selberg integral -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealEqualConvergence

open Langlands.Archimedean (unitaryCompact)
open Langlands.RankinSelberg (LeftUnipotentQuotient lastRow)
open Langlands.QuotientIntegration (descend)
open ArchimedeanLocal RealIwasawa RealConvergenceAnalysis

local instance realConvGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
local instance realConvGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
local instance realConvNMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
local instance realConvNBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := ⟨rfl⟩
local instance realConvQMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
local instance realConvQBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

variable {r : ℕ}

/-! ### Hypothesis shapes -/

/-- The shape of the gauge estimate `RealWhittakerGauge.exists_gauge_bound`: arbitrarily fast
exponential decay in the positive simple-root coordinates on `torus y * k`, with a fixed
exponential growth in `∑ |y_j|`. -/
def HasGauge (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) : Prop :=
  ∃ N : ℕ, ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (y : Fin (r + 1) → ℝ) (k : unitaryCompact ℝ (r + 1)),
      ‖W (torus y * (k : Langlands.GeneralLinear (r + 1) ℝ))‖ ≤
        C * Real.exp (-(M : ℝ) * rootPos y + (N : ℝ) * ∑ j, |y j|)

/-- Rapid decay of a function on `ℝⁿ`: `‖x‖^k ‖Φ x‖` is bounded for every `k`. -/
def HasRapidDecay {n : ℕ} (Φ : (Fin n → ℝ) → ℂ) : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ k * ‖Φ x‖ ≤ C

/-! ### Functions on the quotient -/

/-- The function `g ↦ W(g) W'(g) Φ(e_n g)` on `GL_(r+1)(ℝ)`. -/
def kernel (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (Φ : (Fin (r + 1) → ℝ) → ℂ)
    (g : Langlands.GeneralLinear (r + 1) ℝ) : ℂ :=
  W g * W' g * Φ (lastRow g)

/-- `log |det g|`. -/
def logDet (g : Langlands.GeneralLinear (r + 1) ℝ) : ℝ :=
  Real.log (realNormalizedAbs (Matrix.det g.val))

theorem kernel_unipotent_mul {W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    {Φ : (Fin (r + 1) → ℝ) → ℂ}
    (hinv : ∀ u ∈ Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g,
      W (u * g) * W' (u * g) = W g * W' g)
    (u : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ)
    (g : Langlands.GeneralLinear (r + 1) ℝ) :
    kernel W W' Φ (u.val * g) = kernel W W' Φ g := by
  unfold kernel
  rw [hinv u.val u.2 g, Langlands.RankinSelberg.lastRow_unipotent_mul]

theorem logDet_unipotent_mul (u : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ)
    (g : Langlands.GeneralLinear (r + 1) ℝ) : logDet (u.val * g) = logDet g := by
  unfold logDet
  rw [Units.val_mul, Matrix.det_mul, Langlands.RankinSelberg.unipotent_det, one_mul]

theorem out_eq_descend {A : Type*} (f : Langlands.GeneralLinear (r + 1) ℝ → A)
    (hf : ∀ h : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g, f (h.val * g) = f g)
    (q : LeftUnipotentQuotient r ℝ) :
    f q.out = descend (Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ) f hf q := by
  conv_rhs => rw [← Quotient.out_eq q]
  rfl

theorem eq_torus_mul_kpart {A : Type*} (f : Langlands.GeneralLinear (r + 1) ℝ → A)
    (hf : ∀ h : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g, f (h.val * g) = f g)
    (g : Langlands.GeneralLinear (r + 1) ℝ) :
    f g = f (torus (alpha g) * (kpart g : Langlands.GeneralLinear (r + 1) ℝ)) := by
  have h := congrArg (descend (Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ) f hf)
    (mk_eq_mk_torus_mul_kpart g)
  rw [Langlands.QuotientIntegration.descend_mk, Langlands.QuotientIntegration.descend_mk] at h
  exact h

theorem alpha_out (q : LeftUnipotentQuotient r ℝ) : alpha q.out = alphaQ q :=
  out_eq_descend alpha alpha_unipotent_mul q

theorem continuous_descend {f : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hf : ∀ h : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g, f (h.val * g) = f g)
    (hc : Continuous f) :
    Continuous (descend (Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ) f hf) := by
  unfold descend
  exact hc.quotient_lift _

theorem continuous_descend_real {f : Langlands.GeneralLinear (r + 1) ℝ → ℝ}
    (hf : ∀ h : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g, f (h.val * g) = f g)
    (hc : Continuous f) :
    Continuous (descend (Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ) f hf) := by
  unfold descend
  exact hc.quotient_lift _

theorem continuous_logDet : Continuous (logDet (r := r)) := by
  have hdet : Continuous fun g : Langlands.GeneralLinear (r + 1) ℝ => Matrix.det g.val :=
    (continuous_id.matrix_det).comp Units.continuous_val
  refine Continuous.log (continuous_abs.comp hdet) fun g => ?_
  exact abs_ne_zero.mpr (Matrix.isUnit_iff_isUnit_det _ |>.mp g.isUnit).ne_zero

/-! ### Values on `torus y * k` -/

theorem abs_det_unitary (k : unitaryCompact ℝ (r + 1)) :
    |Matrix.det ((k : Langlands.GeneralLinear (r + 1) ℝ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)|
      = 1 := by
  have hU : ((k : Langlands.GeneralLinear (r + 1) ℝ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) ∈
      Matrix.unitaryGroup (Fin (r + 1)) ℝ := k.2
  have h := Matrix.det_of_mem_unitary hU
  have h2 := CStarRing.norm_of_mem_unitary h
  rwa [Real.norm_eq_abs] at h2

theorem logDet_torus_mul (y : Fin (r + 1) → ℝ) (k : unitaryCompact ℝ (r + 1)) :
    logDet (torus y * (k : Langlands.GeneralLinear (r + 1) ℝ)) = ∑ j, y j := by
  unfold logDet realNormalizedAbs
  rw [Units.val_mul, torus_val, Matrix.det_mul, Matrix.det_diagonal, abs_mul, abs_det_unitary k,
    mul_one, ← Real.exp_sum, abs_of_pos (Real.exp_pos _), Real.log_exp]

/-- The last row of the orthogonal matrix `k`. -/
def kRow (k : unitaryCompact ℝ (r + 1)) : Fin (r + 1) → ℝ :=
  fun j => ((k : Langlands.GeneralLinear (r + 1) ℝ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)
    (Fin.last r) j

theorem lastRow_torus_mul (y : Fin (r + 1) → ℝ) (k : unitaryCompact ℝ (r + 1)) :
    lastRow (torus y * (k : Langlands.GeneralLinear (r + 1) ℝ)) =
      Real.exp (y (Fin.last r)) • kRow k := by
  funext j
  rw [Pi.smul_apply, smul_eq_mul]
  exact RealWhittakerGauge.torus_mul_val_apply y k (Fin.last r) j

theorem one_le_mul_norm_kRow (k : unitaryCompact ℝ (r + 1)) :
    1 ≤ ((r : ℝ) + 1) * ‖kRow k‖ := by
  set A := ((k : Langlands.GeneralLinear (r + 1) ℝ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)
  have hU : A ∈ Matrix.unitaryGroup (Fin (r + 1)) ℝ := k.2
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hU) (Fin.last r)) (Fin.last r)
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  simp only [Matrix.star_apply, star_trivial] at h
  have hle : ‖kRow k‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
    rw [Real.norm_eq_abs]
    exact RealWhittakerGauge.abs_unitary_entry_le k _ _
  have hj : ∀ j, A (Fin.last r) j * A (Fin.last r) j ≤ ‖kRow k‖ * ‖kRow k‖ := by
    intro j
    rw [← abs_mul_abs_self]
    have h1 := norm_le_pi_norm (kRow k) j
    rw [Real.norm_eq_abs] at h1
    exact mul_self_le_mul_self (abs_nonneg _) h1
  have hsum : (1 : ℝ) ≤ ((r : ℝ) + 1) * (‖kRow k‖ * ‖kRow k‖) := by
    calc
      (1 : ℝ) = ∑ j, A (Fin.last r) j * A (Fin.last r) j := h.symm
      _ ≤ ∑ _j : Fin (r + 1), ‖kRow k‖ * ‖kRow k‖ := Finset.sum_le_sum fun j _ => hj j
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
  have h0 : 0 ≤ ‖kRow k‖ := norm_nonneg _
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  nlinarith

theorem exp_le_mul_norm_lastRow (y : Fin (r + 1) → ℝ) (k : unitaryCompact ℝ (r + 1)) :
    Real.exp (y (Fin.last r)) ≤
      ((r : ℝ) + 1) * ‖lastRow (torus y * (k : Langlands.GeneralLinear (r + 1) ℝ))‖ := by
  rw [lastRow_torus_mul, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h := one_le_mul_norm_kRow k
  have he := Real.exp_pos (y (Fin.last r))
  nlinarith

/-! ### Rapid decay of `Φ` along the last row -/

theorem exists_norm_le_exp {n : ℕ} {Φ : (Fin n → ℝ) → ℂ} (hΦ : HasRapidDecay Φ) {c : ℝ}
    (hc : 0 < c) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Fin n → ℝ) (m : ℝ), Real.exp m ≤ c * ‖x‖ →
      ‖Φ x‖ ≤ C * Real.exp (-(K : ℝ) * max m 0) := by
  obtain ⟨C0, h0⟩ := hΦ 0
  obtain ⟨CK, hK⟩ := hΦ K
  have hC0 : 0 ≤ C0 := by
    have := h0 0
    rw [pow_zero, one_mul] at this
    exact (norm_nonneg _).trans this
  have hCK : 0 ≤ CK := (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)).trans (hK 0)
  have hcK : 0 ≤ c ^ K := pow_nonneg hc.le K
  refine ⟨C0 + CK * c ^ K, add_nonneg hC0 (mul_nonneg hCK hcK), fun x m hx => ?_⟩
  rcases le_or_gt m 0 with hm | hm
  · rw [max_eq_right hm, mul_zero, Real.exp_zero, mul_one]
    have := h0 x
    rw [pow_zero, one_mul] at this
    nlinarith [mul_nonneg hCK hcK]
  · rw [max_eq_left hm.le]
    have h1 : Real.exp ((K : ℝ) * m) ≤ c ^ K * ‖x‖ ^ K := by
      rw [Real.exp_nat_mul, ← mul_pow]
      exact pow_le_pow_left₀ (Real.exp_pos _).le hx K
    have h2 : ‖Φ x‖ * Real.exp ((K : ℝ) * m) ≤ c ^ K * CK := by
      calc
        ‖Φ x‖ * Real.exp ((K : ℝ) * m) ≤ ‖Φ x‖ * (c ^ K * ‖x‖ ^ K) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = c ^ K * (‖x‖ ^ K * ‖Φ x‖) := by ring
        _ ≤ c ^ K * CK := mul_le_mul_of_nonneg_left (hK x) hcK
    calc
      ‖Φ x‖ = ‖Φ x‖ * Real.exp ((K : ℝ) * m) * Real.exp (-(K : ℝ) * m) := by
        rw [mul_assoc, ← Real.exp_add, show (K : ℝ) * m + -(K : ℝ) * m = 0 by ring,
          Real.exp_zero, mul_one]
      _ ≤ (c ^ K * CK) * Real.exp (-(K : ℝ) * m) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ ≤ (C0 + CK * c ^ K) * Real.exp (-(K : ℝ) * m) :=
        mul_le_mul_of_nonneg_right (by nlinarith) (Real.exp_pos _).le

/-! ### Integrability from a bound in toral coordinates -/

theorem continuous_rootPos : Continuous (rootPos (r := r)) := by
  unfold rootPos
  exact continuous_finsetSum _ fun i _ => by fun_prop

theorem linear_le (L : (Fin (r + 1) → ℝ) →L[ℝ] ℝ) (y : Fin (r + 1) → ℝ) :
    L y ≤ ‖L‖ * ∑ j, |y j| := by
  have h1 : L y ≤ ‖L‖ * ‖y‖ := (le_abs_self _).trans (by
    rw [← Real.norm_eq_abs]
    exact L.le_opNorm y)
  have h2 : ‖y‖ ≤ ∑ j, |y j| := by
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)).mpr
      fun j => ?_
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun j => |y j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ j)
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))

/-- **Integrability criterion.** Suppose integration against `ν` in the toral coordinate
`alphaQ` is integration against `κ exp(L x) dx`. Then a measurable function on the quotient
bounded by `C exp(−M · rootPos y + A ∑ |y_j| + t ∑ y_j − K max(y_r, 0))` at `y = alphaQ q` is
integrable as soon as `t`, `M`, `K` are large compared with `A + ‖L‖`. -/
theorem integrable_of_toral_bound {ν : Measure (LeftUnipotentQuotient r ℝ)} {κ : ℝ≥0}
    {L : (Fin (r + 1) → ℝ) →L[ℝ] ℝ}
    (hκL : ∀ B : (Fin (r + 1) → ℝ) → ℝ≥0∞, Measurable B →
      ∫⁻ q, B (alphaQ q) ∂ν = (κ : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (Real.exp (L x)) * B x)
    {h : LeftUnipotentQuotient r ℝ → ℝ} (hm : AEStronglyMeasurable h ν)
    {C A t M K : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A)
    (ht : (A + ‖L‖ + 1) * ((r : ℝ) + 1) ≤ t)
    (hM : (A + ‖L‖ + 1) * ((r : ℝ) + 1) + t * ((r : ℝ) + 1) ≤ M)
    (hK : (A + ‖L‖ + 1) * ((r : ℝ) + 1) + t * ((r : ℝ) + 1) ≤ K)
    (hb : ∀ q, ‖h q‖ ≤ C * Real.exp (-M * rootPos (alphaQ q) + A * ∑ j, |alphaQ q j| +
      t * ∑ j, alphaQ q j - K * max (alphaQ q (Fin.last r)) 0)) :
    Integrable h ν := by
  refine ⟨hm, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  set E : (Fin (r + 1) → ℝ) → ℝ := fun y => -M * rootPos y + A * ∑ j, |y j| +
    t * ∑ j, y j - K * max (y (Fin.last r)) 0 with hE
  have hEc : Continuous E := by
    rw [hE]
    have h1 : Continuous fun y : Fin (r + 1) → ℝ => ∑ j, |y j| :=
      continuous_finsetSum _ fun j _ => (continuous_apply j).abs
    have h2 : Continuous fun y : Fin (r + 1) → ℝ => ∑ j, y j :=
      continuous_finsetSum _ fun j _ => continuous_apply j
    exact (((continuous_const.mul continuous_rootPos).add (continuous_const.mul h1)).add
      (continuous_const.mul h2)).sub
      (continuous_const.mul ((continuous_apply _).max continuous_const))
  set B : (Fin (r + 1) → ℝ) → ℝ≥0∞ := fun y => ENNReal.ofReal (C * Real.exp (E y)) with hB
  have hBm : Measurable B :=
    ENNReal.measurable_ofReal.comp
      ((continuous_const.mul (Real.continuous_exp.comp hEc)).measurable)
  have hL0 : 0 ≤ ‖L‖ := norm_nonneg _
  have hpt : ∀ y, ENNReal.ofReal (Real.exp (L y)) * B y ≤
      ENNReal.ofReal C * ENNReal.ofReal (Real.exp (-1 * ∑ j, |y j|)) := by
    intro y
    rw [hB, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul' (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    have hexp : L y + E y ≤ -1 * ∑ j, |y j| := by
      have h1 := linear_le L y
      have h2 := exponent_le y (A := A + ‖L‖) (t := t) (M := M) (K := K) (by positivity) ht hM hK
      rw [hE]
      simp only
      nlinarith
    calc
      Real.exp (L y) * (C * Real.exp (E y)) = C * Real.exp (L y + E y) := by
        rw [Real.exp_add]
        ring
      _ ≤ C * Real.exp (-1 * ∑ j, |y j|) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hC
  calc
    ∫⁻ q, ENNReal.ofReal ‖h q‖ ∂ν ≤ ∫⁻ q, B (alphaQ q) ∂ν :=
      lintegral_mono fun q => ENNReal.ofReal_le_ofReal (hb q)
    _ = (κ : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (Real.exp (L x)) * B x := hκL B hBm
    _ ≤ (κ : ℝ≥0∞) * ∫⁻ x : Fin (r + 1) → ℝ, ENNReal.ofReal C *
          ENNReal.ofReal (Real.exp (-1 * ∑ j, |x j|)) :=
      mul_le_mul_right (lintegral_mono hpt) _
    _ = (κ : ℝ≥0∞) * (ENNReal.ofReal C *
          ∫⁻ x : Fin (r + 1) → ℝ, ENNReal.ofReal (Real.exp (-1 * ∑ j, |x j|))) := by
      rw [lintegral_const_mul]
      exact ENNReal.measurable_ofReal.comp ((Real.continuous_exp.comp
        (continuous_const.mul (continuous_finsetSum _ fun j _ =>
          (continuous_apply j).abs))).measurable)
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (lintegral_exp_neg_mul_sum_abs_lt_top one_pos))


/-! ### Convergence and holomorphy -/

theorem continuous_kernel {W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    {Φ : (Fin (r + 1) → ℝ) → ℂ} (hW : Continuous W) (hW' : Continuous W')
    (hΦ : Continuous Φ) : Continuous (kernel W W' Φ) := by
  have hrow : Continuous (lastRow : Langlands.GeneralLinear (r + 1) ℝ → Fin (r + 1) → ℝ) :=
    continuous_pi fun j => (Langlands.GeneralLinear.entry (Fin.last r) j).continuous
  exact (hW.mul hW').mul (hΦ.comp hrow)

/-- The integrand of `Ψ(s; W, W', Φ)` is `kernel(q.out) · exp(s · logDet(q.out))`. -/
theorem realEqualIntegrand_eq (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (Φ : (Fin (r + 1) → ℝ) → ℂ) (s : ℂ) :
    realEqualIntegrand W W' Φ s =
      fun q => kernel W W' Φ q.out * Complex.exp (s * (logDet q.out : ℂ)) :=
  rfl

/-- **Convergence and holomorphy of the real equal-rank integral.** Let `W`, `W'` be continuous,
with `W(ug) W'(ug) = W(g) W'(g)` for upper unipotent `u`, both satisfying the gauge estimate,
and let `Φ` be continuous of rapid decay. Then there is `σ` such that the integrand of
`Ψ(s; W, W', Φ)` is integrable for `Re s > σ` and `Ψ(·; W, W', Φ)` is holomorphic there. -/
theorem exists_convergence (D : RealQuotientMeasureData r)
    {W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ} {Φ : (Fin (r + 1) → ℝ) → ℂ}
    (hW : Continuous W) (hW' : Continuous W') (hΦc : Continuous Φ)
    (hinv : ∀ u ∈ Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g,
      W (u * g) * W' (u * g) = W g * W' g)
    (hgW : HasGauge W) (hgW' : HasGauge W') (hΦ : HasRapidDecay Φ) :
    ∃ σ : ℝ, (∀ s : ℂ, σ < s.re → Integrable (realEqualIntegrand W W' Φ s) D.measure) ∧
      DifferentiableOn ℂ (realEqualIntegral D W W' Φ) {s : ℂ | σ < s.re} := by
  have := D.groupHaar_isHaar
  have := D.unipotentHaar_isHaar
  have := D.unipotentHaar_rightInvariant
  obtain ⟨κ, L, hκL⟩ :=
    exists_lintegral_alphaQ D.groupHaar D.unipotentHaar D.measure D.compatible
  obtain ⟨N1, hN1⟩ := hgW
  obtain ⟨N2, hN2⟩ := hgW'
  obtain ⟨C2, hC2, hb2⟩ := hN2 0
  have hA0 : (0 : ℝ) ≤ (N1 : ℝ) + N2 := by positivity
  have hkinv : ∀ h : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g,
      kernel W W' Φ (h.val * g) = kernel W W' Φ g := fun h g => kernel_unipotent_mul hinv h g
  have hlinv : ∀ h : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g,
      logDet (h.val * g) = logDet g := fun h g => logDet_unipotent_mul h g
  let f : LeftUnipotentQuotient r ℝ → ℂ := fun q => kernel W W' Φ q.out
  let ℓ : LeftUnipotentQuotient r ℝ → ℝ := fun q => logDet q.out
  have hfc : Continuous f := by
    have hfe : f = descend (Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ)
        (kernel W W' Φ) hkinv := funext fun q => out_eq_descend _ hkinv q
    rw [hfe]
    exact continuous_descend hkinv (continuous_kernel hW hW' hΦc)
  have hℓc : Continuous ℓ := by
    have hℓe : ℓ = descend (Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ)
        logDet hlinv := funext fun q => out_eq_descend _ hlinv q
    rw [hℓe]
    exact continuous_descend_real hlinv continuous_logDet
  have hfq : ∀ q, f q = kernel W W' Φ
      (torus (alphaQ q) * (kpart q.out : Langlands.GeneralLinear (r + 1) ℝ)) := by
    intro q
    rw [← alpha_out q]
    exact eq_torus_mul_kpart (kernel W W' Φ) hkinv q.out
  have hℓq : ∀ q, ℓ q = ∑ j, alphaQ q j := by
    intro q
    rw [← alpha_out q, ← logDet_torus_mul (alpha q.out) (kpart q.out)]
    exact eq_torus_mul_kpart logDet hlinv q.out
  set σ : ℝ := ((N1 : ℝ) + N2 + ‖L‖ + 1) * ((r : ℝ) + 1) with hσ
  have hint : ∀ t : ℝ, σ < t →
      Integrable (fun q => ‖f q‖ * Real.exp (t * ℓ q)) D.measure := by
    intro t ht
    set M : ℕ := ⌈((N1 : ℝ) + N2 + ‖L‖ + 1) * ((r : ℝ) + 1) + t * ((r : ℝ) + 1)⌉₊ with hM
    obtain ⟨C1, hC1, hb1⟩ := hN1 M
    obtain ⟨C3, hC3, hb3⟩ := exists_norm_le_exp hΦ (c := (r : ℝ) + 1) (by positivity) M
    refine integrable_of_toral_bound hκL
      ((hfc.norm.mul (Real.continuous_exp.comp (continuous_const.mul hℓc))).aestronglyMeasurable)
      (C := C1 * C2 * C3) (A := (N1 : ℝ) + N2) (t := t) (M := (M : ℝ)) (K := (M : ℝ))
      (by positivity) hA0 ht.le (Nat.le_ceil _) (Nat.le_ceil _) fun q => ?_
    set y := alphaQ q with hy
    set k := kpart q.out with hk
    set x := torus y * (k : Langlands.GeneralLinear (r + 1) ℝ) with hx
    have hW1 := hb1 y k
    have hW2 := hb2 y k
    have hΦ3 := hb3 (lastRow x) (y (Fin.last r)) (exp_le_mul_norm_lastRow y k)
    have hker : ‖kernel W W' Φ x‖ ≤
        (C1 * Real.exp (-(M : ℝ) * rootPos y + (N1 : ℝ) * ∑ j, |y j|)) *
          (C2 * Real.exp (-((0 : ℕ) : ℝ) * rootPos y + (N2 : ℝ) * ∑ j, |y j|)) *
          (C3 * Real.exp (-(M : ℝ) * max (y (Fin.last r)) 0)) := by
      unfold kernel
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul hW1 hW2 (norm_nonneg _) (by positivity)) hΦ3
        (norm_nonneg _) (by positivity)
    have hexp : Real.exp (-(M : ℝ) * rootPos y + (N1 : ℝ) * ∑ j, |y j|) *
        Real.exp (-((0 : ℕ) : ℝ) * rootPos y + (N2 : ℝ) * ∑ j, |y j|) *
        Real.exp (-(M : ℝ) * max (y (Fin.last r)) 0) * Real.exp (t * ∑ j, y j) =
        Real.exp (-(M : ℝ) * rootPos y + ((N1 : ℝ) + N2) * ∑ j, |y j| + t * ∑ j, y j -
          (M : ℝ) * max (y (Fin.last r)) 0) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le),
      hfq q, hℓq q]
    calc
      ‖kernel W W' Φ x‖ * Real.exp (t * ∑ j, y j) ≤
          ((C1 * Real.exp (-(M : ℝ) * rootPos y + (N1 : ℝ) * ∑ j, |y j|)) *
            (C2 * Real.exp (-((0 : ℕ) : ℝ) * rootPos y + (N2 : ℝ) * ∑ j, |y j|)) *
            (C3 * Real.exp (-(M : ℝ) * max (y (Fin.last r)) 0))) *
            Real.exp (t * ∑ j, y j) :=
        mul_le_mul_of_nonneg_right hker (Real.exp_pos _).le
      _ = C1 * C2 * C3 * (Real.exp (-(M : ℝ) * rootPos y + (N1 : ℝ) * ∑ j, |y j|) *
            Real.exp (-((0 : ℕ) : ℝ) * rootPos y + (N2 : ℝ) * ∑ j, |y j|) *
            Real.exp (-(M : ℝ) * max (y (Fin.last r)) 0) * Real.exp (t * ∑ j, y j)) := by
        ring
      _ = _ := by rw [hexp]
  refine ⟨σ, fun s hs => ?_, ?_⟩
  · have hmeas : AEStronglyMeasurable (realEqualIntegrand W W' Φ s) D.measure := by
      rw [realEqualIntegrand_eq]
      exact (hfc.mul (Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp hℓc)))).aestronglyMeasurable
    refine (hint s.re hs).mono' hmeas (Filter.Eventually.of_forall fun q => ?_)
    rw [realEqualIntegrand_eq]
    show ‖f q * Complex.exp (s * (ℓ q : ℂ))‖ ≤ ‖f q‖ * Real.exp (s.re * ℓ q)
    rw [norm_mul, norm_cexp_mul_ofReal]
  · exact differentiableOn_integral_cexp_mul (f := f) (ℓ := ℓ) hfc.aestronglyMeasurable
      hℓc.aestronglyMeasurable hint

/-! ### Functions with uniformly regular derivatives -/

section Regular

open RealLocalWhittaker (iteratedRightDerivative regularFunctions)

theorem realWhittakerCharacter_mul_neg (a : ℝˣ) (u : Langlands.GeneralLinear (r + 1) ℝ) :
    realWhittakerCharacter a u * realWhittakerCharacter (-a) u = 1 := by
  unfold realWhittakerCharacter
  simp only [HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
    LocalFactor.Archimedean.realScaledCharacter_apply, Real.fourierChar_apply, Units.val_neg]
  rw [← Complex.exp_add]
  convert Complex.exp_zero using 2
  push_cast
  ring

theorem hasRapidDecay_schwartz {n : ℕ} (Φ : SchwartzMap (Fin n → ℝ) ℂ) : HasRapidDecay Φ := by
  intro k
  obtain ⟨C, -, hC⟩ := Φ.decay k 0
  refine ⟨C, fun x => ?_⟩
  have h := hC x
  rwa [norm_iteratedFDeriv_zero] at h

set_option backward.isDefEq.respectTransparency false in
/-- **Convergence and holomorphy for uniformly regular functions.** If all iterated right
derivatives of `W` (resp. `W'`) lie in `regularFunctions r a` (resp. `regularFunctions r (-a)`)
and are polynomially bounded with one common exponent, then for every Schwartz function `Φ` the
integral `Ψ(s; W, W', Φ)` converges absolutely and is holomorphic on a right half-plane. -/
theorem exists_convergence_of_regular (D : RealQuotientMeasureData r) {a : ℝˣ}
    {W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ} (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ)
    (hreg : ∀ Xs, iteratedRightDerivative r Xs W ∈ regularFunctions r a)
    (hgrowth : ∃ N : ℕ, ∀ Xs, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖iteratedRightDerivative r Xs W g‖ ≤ C * realMatrixHeight g ^ N)
    (hreg' : ∀ Xs, iteratedRightDerivative r Xs W' ∈ regularFunctions r (-a))
    (hgrowth' : ∃ N : ℕ, ∀ Xs, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖iteratedRightDerivative r Xs W' g‖ ≤ C * realMatrixHeight g ^ N) :
    ∃ σ : ℝ, (∀ s : ℂ, σ < s.re → Integrable (realEqualIntegrand W W' Φ s) D.measure) ∧
      DifferentiableOn ℂ (realEqualIntegral D W W' Φ) {s : ℂ | σ < s.re} := by
  have hW : W ∈ regularFunctions r a := hreg []
  have hW' : W' ∈ regularFunctions r (-a) := hreg' []
  have hinv : ∀ u ∈ Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g,
      W (u * g) * W' (u * g) = W g * W' g := by
    intro u hu g
    rw [hW.1 u hu g, hW'.1 u hu g]
    calc
      realWhittakerCharacter a u * W g * (realWhittakerCharacter (-a) u * W' g) =
          (realWhittakerCharacter a u * realWhittakerCharacter (-a) u) * (W g * W' g) := by
        ring
      _ = W g * W' g := by rw [realWhittakerCharacter_mul_neg, one_mul]
  exact exists_convergence D hW.2.1.continuous hW'.2.1.continuous Φ.continuous hinv
    (RealWhittakerGauge.exists_gauge_bound hreg hgrowth)
    (RealWhittakerGauge.exists_gauge_bound hreg' hgrowth') (hasRapidDecay_schwartz Φ)

end Regular

end Langlands.Global.RankinSelbergGlobal.RealEqualConvergence

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal

local instance realConvStatementGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
local instance realConvStatementGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
local instance realConvStatementNMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
local instance realConvStatementNBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := ⟨rfl⟩
local instance realConvStatementQMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.RankinSelberg.LeftUnipotentQuotient n ℝ) := borel _
local instance realConvStatementQBorel (n : ℕ) :
    BorelSpace (Langlands.RankinSelberg.LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

/-- **Convergence and holomorphy of the real equal-rank Rankin–Selberg integral**
(Jacquet 2009, Theorem 2.1(i) and the holomorphy in (ii), real equal-rank case, for Whittaker
functions with uniformly bounded derivatives). Let `W` and `W'` be functions on `GL_(r+1)(ℝ)`
all of whose iterated right derivatives are smooth, transform on the left under the upper
unipotent group by the characters for `a` and `-a` respectively, and are bounded by a constant
times a fixed power (independent of the derivative) of the matrix height. Then for every
Schwartz function `Φ` there is `σ` such that the integrand of `Ψ(s; W, W', Φ)` is integrable for
the quotient measure of `D` whenever `Re s > σ`, and `s ↦ Ψ(s; W, W', Φ)` is holomorphic on
`Re s > σ`. -/
def RealEqualConvergenceStatement : Prop :=
  ∀ (r : ℕ) (D : RealQuotientMeasureData r) (a : ℝˣ)
    (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ),
    (∀ Xs, RealLocalWhittaker.iteratedRightDerivative r Xs W ∈
      RealLocalWhittaker.regularFunctions r a) →
    (∃ N : ℕ, ∀ Xs, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖RealLocalWhittaker.iteratedRightDerivative r Xs W g‖ ≤ C * realMatrixHeight g ^ N) →
    (∀ Xs, RealLocalWhittaker.iteratedRightDerivative r Xs W' ∈
      RealLocalWhittaker.regularFunctions r (-a)) →
    (∃ N : ℕ, ∀ Xs, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖RealLocalWhittaker.iteratedRightDerivative r Xs W' g‖ ≤ C * realMatrixHeight g ^ N) →
    ∃ σ : ℝ, (∀ s : ℂ, σ < s.re → Integrable (realEqualIntegrand W W' Φ s) D.measure) ∧
      DifferentiableOn ℂ (realEqualIntegral D W W' Φ) {s : ℂ | σ < s.re}

theorem realEqualConvergence : RealEqualConvergenceStatement :=
  fun _ D _ _ _ Φ hreg hgrowth hreg' hgrowth' =>
    RealEqualConvergence.exists_convergence_of_regular D Φ hreg hgrowth hreg' hgrowth'

end Langlands.Global.RankinSelbergGlobal
