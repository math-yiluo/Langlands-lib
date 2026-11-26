import Langlands.Global.RankinSelberg.RealTemperedOrdinaryConvergence
import Langlands.Global.RankinSelberg.RealUnequalDualFamily

/-! # Sharp convergence of the reflected real rectangular integral -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealTemperedWhittaker

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (lowerBlockFirst lowerBlockMiddle lowerBlockLast)
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure)
open ArchimedeanLocal RealIwasawa RealConvergenceAnalysis RealEqualConvergence RealRectangularIwasawa
open RealUnequalDualConvergence (rootPos_cast sum_abs_cast rect_size rectangularPoint_eq
  rectDecay exp_neg_mul_log_le integrable_rectDecay sigmaFinite_rect)
open RealUnequalConvergence (padVec extVec extVec_fin extVec_of_le)
open RealUnequalFamily (HasLeftCharacter dualProduct_unipotent_mul continuous_dualKernel dualIntegral_eq_prod)
open RealLocalWhittaker (regularFunctions)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable
  archimedeanRealQBorel

variable {r t : ℕ}
local notation "G" => fun r => Langlands.GeneralLinear (r + 1) ℝ
local notation "Rect" => Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℝ

private theorem alpha_rectangularPoint_eq (h : t < r) (y : Fin (t + 1) → ℝ)
    (k : unitaryCompact ℝ (t + 1)) (x : Rect) :
    alpha (ArchimedeanLocal.rectangularPoint h (torus y * k.val) x) =
      fun i => zc y k x (Fin.cast (rect_size h).symm i) := by
  rw [rectangularPoint_eq]
  exact alpha_reindex_finCongr (rect_size h) _

private theorem abs_alpha_rectangularPoint_sub (h : t < r) (y : Fin (t + 1) → ℝ)
    (k : unitaryCompact ℝ (t + 1)) (x : Rect) (i : Fin (r + 1)) :
    |alpha (ArchimedeanLocal.rectangularPoint h (torus y * k.val) x) i - padVec r y i| ≤
      Real.log (1 + frob x) / 2 := by
  rw [alpha_rectangularPoint_eq h]
  let j := Fin.cast (rect_size h).symm i
  change |zc y k x j - extVec y j.val| ≤ _
  have hΛ : 0 ≤ Real.log (1 + frob x) := Real.log_nonneg (by linarith [frob_nonneg x])
  rcases RealUnequalPairConvergence.index_cases j with ⟨p, hp⟩ | ⟨l, hl⟩ | hl
  · rw [hp]
    have hv : (lowerBlockFirst (r - (t + 1)) 1 p).val = p.val := rfl
    rw [hv, extVec_fin]
    rw [abs_le]
    constructor <;> linarith [first_upper y k x p, first_lower y k x p]
  · rw [hl]
    have hv : (lowerBlockMiddle (t + 1) 1 l).val = t + 1 + l.val := rfl
    rw [hv, extVec_of_le y (by omega), sub_zero, abs_of_nonneg (middle_lower y k x l)]
    linarith [middle_upper y k x l]
  · rw [hl]
    have hv : (lowerBlockLast (t + 1) (r - (t + 1)) (0 : Fin 1)).val =
        t + 1 + (r - (t + 1)) := by simp [lowerBlockLast]
    rw [hv, extVec_of_le y (by omega), last_eq, sub_zero, abs_zero]
    positivity

private theorem modulus_rectangularPoint_le (h : t < r) (y : Fin (t + 1) → ℝ)
    (k : unitaryCompact ℝ (t + 1)) (x : Rect) :
    torusModularLog (r + 1) (alpha (ArchimedeanLocal.rectangularPoint h (torus y * k.val) x)) ≤
      torusModularLog (r + 1) (padVec r y) +
        ((r : ℝ) + 1) * r * (Real.log (1 + frob x) / 2) := by
  apply sub_le_iff_le_add'.mp
  simp only [torusModularLog_apply, Nat.cast_succ, add_sub_cancel_right,
    ← Finset.sum_sub_distrib, ← mul_sub]
  calc
    _ ≤ ∑ _i : Fin (r + 1), (r : ℝ) * (Real.log (1 + frob x) / 2) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hi : (i.val : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.le_of_lt_succ i.isLt
      have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
      have hc : |(r : ℝ) - 2 * i.val| ≤ r := abs_le.mpr
        ⟨by linarith, by linarith⟩
      exact (le_abs_self _).trans (by
        rw [abs_mul]
        exact mul_le_mul hc (abs_alpha_rectangularPoint_sub h y k x i)
          (abs_nonneg _) (Nat.cast_nonneg _))
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]; ring

theorem HasTemperedGauge.translate {W : G r → ℂ} (hW : HasTemperedGauge W)
    {k₀ : G r} (hk₀ : k₀ ∈ unitaryCompact ℝ (r + 1)) :
    HasTemperedGauge (ArchimedeanLocal.translateFunction k₀ W) := by
  intro ε hε M
  obtain ⟨C, hC, hb⟩ := hW ε hε M
  refine ⟨C, hC, fun y k => ?_⟩
  simpa only [ArchimedeanLocal.translateFunction, mul_assoc] using
    hb y ⟨k.val * k₀, (unitaryCompact ℝ (r + 1)).mul_mem k.property hk₀⟩

private theorem rect_gauge (h : t < r) {W : G r → ℂ} (hW : HasTemperedGauge W)
    (hAbs : ∀ u ∈ Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g, ‖W (u * g)‖ = ‖W g‖)
    {ε : ℝ} (hε : 0 < ε) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : Fin (t + 1) → ℝ) (k : unitaryCompact ℝ (t + 1)) (x : Rect),
      ‖W (ArchimedeanLocal.rectangularPoint h (torus y * k.val) x)‖ ≤
        C * Real.exp (torusModularLog (r + 1) (padVec r y) / 2 +
          ε * (∑ i, |y i|) - (J : ℝ) * (∑ j, max (y j) 0) +
          (((r : ℝ) + 1) * r / 4 + ε * ((t : ℝ) + 1 + ((r - (t + 1) : ℕ) : ℝ)) -
            (J : ℝ) * ((t : ℝ) + 1) / 2) * Real.log (1 + frob x)) := by
  let d := r - (t + 1)
  obtain ⟨C, hC, hb⟩ := hW ε hε (((t + 1) + 2 * (t + 1) * d) * J)
  refine ⟨C, hC, fun y k x => ?_⟩
  let g := ArchimedeanLocal.rectangularPoint h (torus y * k.val) x
  have hg : ‖W g‖ = ‖W (torus (alpha g) * (kpart g).val)‖ := by
    conv_lhs => rw [← npart_mul_torus_mul_kpart g, mul_assoc, hAbs _ (npart g).2]
  change ‖W g‖ ≤ _
  rw [hg]
  refine (hb (alpha g) (kpart g)).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC)
  have hmod := modulus_rectangularPoint_le h y k x
  change torusModularLog (r + 1) (alpha g) ≤ _ at hmod
  have hsum := RealRectangularIwasawa.sum_abs_le y k x
  have hdec := decay_le y k x
  rw [show alpha g = fun i => zc y k x (Fin.cast (rect_size h).symm i) from
    alpha_rectangularPoint_eq h y k x, rootPos_cast (rect_size h), sum_abs_cast (rect_size h)]
  rw [← alpha_rectangularPoint_eq h y k x]
  change torusModularLog (r + 1) (alpha g) / 2 + _ - _ ≤ _
  have h1 := mul_le_mul_of_nonneg_left hsum hε.le
  have h2 := mul_le_mul_of_nonneg_left hdec (Nat.cast_nonneg (α := ℝ) J)
  dsimp only [d]
  push_cast at h1 h2 ⊢
  nlinarith only [hmod, h1, h2]

private theorem rectangular_exponent_le {n : ℕ} (y : Fin n → ℝ) {τ J : ℝ}
    (hJ : 2 * τ ≤ J) :
    -(J * ∑ i, max (y i) 0) + τ / 2 * ∑ i, |y i| + τ * ∑ i, y i ≤
      -(τ / 2 * ∑ i, |y i|) := by
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rcases le_or_gt 0 (y i) with hi | hi
  · rw [abs_of_nonneg hi, max_eq_left hi]
    nlinarith only [mul_le_mul_of_nonneg_right hJ hi]
  · rw [abs_of_neg hi, max_eq_right hi.le]
    ring_nf
    exact le_rfl

/-- Opposite-character regular functions with tempered gauges give absolute convergence
and holomorphy of the reflected unequal-rank integral on `Re s > 0`. -/
def RealTemperedBlockConvergenceStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (D : RealQuotientMeasureData t) (a : ℝˣ)
    (W : G r → ℂ) (V : G t → ℂ), W ∈ regularFunctions r a → V ∈ regularFunctions t (-a) →
    HasTemperedGauge W → HasTemperedGauge V →
    (∀ s : ℂ, 0 < s.re → Integrable (realUnequalDualKernel h W V s) (realUnequalDualMeasure a D)) ∧
    DifferentiableOn ℂ (realUnequalDualIntegral h a D W V) {s : ℂ | 0 < s.re}

set_option maxHeartbeats 1400000 in
theorem realTemperedBlockConvergence : RealTemperedBlockConvergenceStatement := by
  intro r t h D a W V hW hV hWg hVg
  let U := ArchimedeanLocal.translateFunction (ArchimedeanLocal.unfoldingWeyl h)
    (ArchimedeanLocal.dualFunction (r + 1) W)
  let U' := ArchimedeanLocal.dualFunction (t + 1) V
  let μ := realUnequalDualMeasure (r := r) a D
  let f := realUnequalDualKernel h W V 0
  let ℓ (q : LeftUnipotentQuotient t ℝ) := logDet q.out
  let c₀ : ℝ := ((r - t : ℕ) : ℝ) / 2
  have hWchar : HasLeftCharacter a W := hW.1
  have hVchar : HasLeftCharacter (-a) V := hV.1
  have hU := hWg.dual.translate (RealUnequalPairConvergence.unfoldingWeyl_mem_unitary h)
  have hU' := hVg.dual
  have hAbs : ∀ u ∈ Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g, ‖U (u * g)‖ = ‖U g‖ :=
    (hWchar.dualTranslate h).norm_eq
  have hfc : Continuous f :=
    continuous_dualKernel h hWchar hVchar hW.2.1.continuous hV.2.1.continuous 0
  have hlinv (u : Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ) (g : G t) :
      logDet (u.val * g) = logDet g := logDet_unipotent_mul u g
  have hℓc : Continuous ℓ :=
    (continuous_descend_real hlinv continuous_logDet).congr
      (fun q => (out_eq_descend logDet hlinv q).symm)
  have hℓ (q : LeftUnipotentQuotient t ℝ) : ℓ q = ∑ j, alphaQ q j := by
    rw [← alpha_out q, ← logDet_torus_mul (alpha q.out) (kpart q.out)]
    exact eq_torus_mul_kpart logDet hlinv q.out
  have hf_norm (p : LeftUnipotentQuotient t ℝ × Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℝ) :
      ‖f p‖ =
        ‖U (ArchimedeanLocal.rectangularPoint h (torus (alphaQ p.1) * (kpart p.1.out).val) p.2)‖ *
          ‖U' (torus (alphaQ p.1) * (kpart p.1.out).val)‖ *
          Real.exp (-c₀ * ∑ j, alphaQ p.1 j) := by
    let F (g : G t) := U (ArchimedeanLocal.rectangularPoint h g p.2) * U' g
    have hFinv (u : Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ) (g : G t) :
        F (u.val * g) = F g := dualProduct_unipotent_mul h hWchar hVchar u g p.2
    have hFq : F p.1.out = F (torus (alphaQ p.1) * (kpart p.1.out).val) := by
      rw [← alpha_out p.1]
      exact eq_torus_mul_kpart F hFinv p.1.out
    change ‖F p.1.out * Complex.exp ((0 - ((r - t : ℕ) : ℂ) / 2) * (ℓ p.1 : ℂ))‖ = _
    rw [hFq, norm_mul, norm_cexp_mul_ofReal, hℓ]
    dsimp only [F]
    rw [norm_mul]
    congr 3
    simp [c₀]
  have heq (s : ℂ) : realUnequalDualKernel h W V s = fun p => f p * Complex.exp (s * (ℓ p.1 : ℂ)) := by
    funext p
    let Y := U (ArchimedeanLocal.rectangularPoint h p.1.out p.2) * U' p.1.out
    change Y * Complex.exp ((s - ((r - t : ℕ) : ℂ) / 2) * (ℓ p.1 : ℂ)) =
      (Y * Complex.exp ((0 - ((r - t : ℕ) : ℂ) / 2) * (ℓ p.1 : ℂ))) *
        Complex.exp (s * (ℓ p.1 : ℂ))
    rw [mul_assoc Y, ← Complex.exp_add]
    congr 2
    ring
  have := D.groupHaar_isHaar
  have := D.unipotentHaar_isHaar
  have := D.unipotentHaar_rightInvariant
  have : SigmaFinite (rectangularMeasure (realSelfDualMeasure a)
    (r - (t + 1)) (t + 1)) := sigmaFinite_rect _ _ _
  obtain ⟨κ, hκ⟩ := realToralQuotientDensity D.groupHaar D.unipotentHaar D.measure D.compatible
  have hint (τ : ℝ) (hτ : 0 < τ) : Integrable
      (fun p => ‖f p‖ * Real.exp (τ * ℓ p.1)) μ := by
    let d := r - (t + 1)
    let m : ℝ := (t : ℝ) + 1
    let ε := τ / 4
    let K := ((r : ℝ) + 1) * r / 4 + ε * (m + d)
    let J : ℕ := ⌈2 * τ + 2 * K + 2 * m * d⌉₊
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hK : 0 ≤ K := by dsimp [K, m]; positivity
    have hm : 1 ≤ m := by dsimp [m]; linarith only [Nat.cast_nonneg (α := ℝ) t]
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    have hJ : 2 * τ + 2 * K + 2 * m * d ≤ (J : ℝ) := Nat.le_ceil _
    have hJ₁ : 2 * τ ≤ J := by linarith [mul_nonneg (by linarith : 0 ≤ m) hd]
    have hJ₂ : m * d ≤ (J : ℝ) * m / 2 - K := by
      nlinarith only [hJ, hτ, mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (α := ℝ) J)]
    obtain ⟨C₁, hC₁, hb₁⟩ := rect_gauge h hU hAbs hε J
    obtain ⟨C₂, hC₂, hb₂⟩ := hU' ε hε 0
    let E (y : Fin (t + 1) → ℝ) := torusModularLog (t + 1) y - τ / 2 * ∑ j, |y j|
    have hE : Continuous E := (torusModularLog (t + 1)).continuous.sub
      (continuous_const.mul (continuous_finsetSum _ fun j _ => (continuous_apply j).abs))
    have hbdy := RealUnequalDualConvergence.integrable_exp_comp_alphaQ_of_le
      (L := -torusModularLog (t + 1)) hκ hE (half_pos hτ) (by
        intro y
        simp only [E, neg_apply]
        linarith)
    have hbd := (hbdy.const_mul (C₁ * C₂)).mul_prod
      (integrable_rectDecay (realSelfDualMeasure a) d (t + 1))
    refine hbd.mono' ((hfc.norm.mul ((Real.continuous_exp.comp
      (continuous_const.mul (hℓc.comp continuous_fst))))).aestronglyMeasurable) (ae_of_all _ fun p => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le), hf_norm, hℓ]
    let y := alphaQ p.1
    let k := kpart p.1.out
    let x := p.2
    let A := torusModularLog (t + 1) y / 2 + ε * ∑ j, |y j|
    let B := c₀ * ∑ j, y j
    let X := (K - (J : ℝ) * m / 2) * Real.log (1 + frob x)
    let Y := (-(J : ℝ) * ∑ i, max (y i) 0) + τ * ∑ j, y j
    have hbW : ‖U (ArchimedeanLocal.rectangularPoint h (torus y * k.val) x)‖ ≤
        C₁ * Real.exp (A + B - (J : ℝ) * (∑ i, max (y i) 0) + X) := by
      refine (hb₁ y k x).trans_eq ?_
      rw [torusModularLog_padVec h]
      congr 2
      simp only [A, B, X, c₀, K, m, d, Nat.cast_sub h.le]
      ring
    have hbV : ‖U' (torus y * k.val)‖ ≤ C₂ * Real.exp A := by
      simpa [A] using hb₂ y k
    have hbX : Real.exp X ≤ rectDecay x := by
      rw [show X = -((J : ℝ) * m / 2 - K) * Real.log (1 + frob x) by dsimp [X]; ring]
      exact exp_neg_mul_log_le x (by simpa only [Nat.cast_succ, m] using hJ₂)
    have hbY : Real.exp (A + A + Y) ≤ Real.exp (E y) := by
      apply Real.exp_le_exp.mpr
      have hy := rectangular_exponent_le y hJ₁
      dsimp only [A, Y, E, ε]
      linarith only [hy]
    calc
      _ ≤ (C₁ * Real.exp (A + B - (J : ℝ) * (∑ i, max (y i) 0) + X)) *
          (C₂ * Real.exp A) * Real.exp (-B) * Real.exp (τ * ∑ j, y j) := by
        have hB : Real.exp (-c₀ * ∑ j, y j) = Real.exp (-B) := by dsimp [B]; ring_nf
        change _ * Real.exp (-c₀ * ∑ j, y j) * Real.exp (τ * ∑ j, y j) ≤ _
        rw [hB]
        gcongr
      _ = C₁ * C₂ * (Real.exp (A + A + Y) * Real.exp X) := by
        rw [← Real.exp_add]
        calc
          _ = C₁ * C₂ * (Real.exp (A + B - (J : ℝ) * (∑ i, max (y i) 0) + X) *
              Real.exp A * Real.exp (-B) * Real.exp (τ * ∑ j, y j)) := by ring
          _ = _ := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
            congr 2
            dsimp only [Y]
            ring
      _ ≤ _ := by
        change _ ≤ C₁ * C₂ * Real.exp (E y) * rectDecay x
        rw [mul_assoc (C₁ * C₂)]
        gcongr
  have hInt (s : ℂ) (hs : 0 < s.re) : Integrable (realUnequalDualKernel h W V s) μ := by
    refine (hint s.re hs).mono'
      ((continuous_dualKernel h hWchar hVchar hW.2.1.continuous hV.2.1.continuous s).aestronglyMeasurable)
      (ae_of_all _ fun p => ?_)
    rw [heq, norm_mul, norm_cexp_mul_ofReal]
  refine ⟨hInt, ?_⟩
  refine (differentiableOn_integral_cexp_mul hfc.aestronglyMeasurable
    (hℓc.comp continuous_fst).aestronglyMeasurable hint).congr (fun s hs => ?_)
  rw [dualIntegral_eq_prod h D a W V s (hInt s hs), heq]
  rfl

end Langlands.Global.RankinSelbergGlobal.RealTemperedWhittaker
