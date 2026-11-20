import Langlands.Global.RankinSelberg.RealUnequalDualConvergence
import Langlands.Global.RankinSelberg.ArchimedeanRealPairFactor
import Langlands.Global.RankinSelberg.RealEqualConvergence

/-!
# Continuation of the real local Rankin–Selberg integrals from Jacquet's pair identity

See the paired Markdown file.
-/

noncomputable section

open MeasureTheory Set Filter Complex
open scoped Topology

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanRealPairIdentity

open Langlands.LocalFactor.Archimedean ArchimedeanMellinPair ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure)

/-! ### Jacquet's pair identity and theta functions -/

/-- Jacquet's pair identity `∫ F h(δ) dμ = ∫ F' k(δ') dμ'` for every measurable rapidly
decreasing pair `(h, k)` with `mellin h (-s) = sign E(s) exp(s² + B s) D(s)` and
`mellin k (s - 1) = exp(s² + B s) Dd(1 - s)` for all `s`, for some real `B`. -/
def PairIdentity {X X' : Type*} [MeasurableSpace X] [MeasurableSpace X']
    (μ : Measure X) (μ' : Measure X') (F : X → ℂ) (δ : X → ℝ) (F' : X' → ℂ) (δ' : X' → ℝ)
    (D Dd E : ℂ → ℂ) (sign : ℂ) : Prop :=
  ∀ (B : ℝ) (h k : ℝ → ℂ), Measurable h → Measurable k → RapidDecay h → RapidDecay k →
    (∀ s : ℂ, mellin h (-s) = sign * E s * Complex.exp (s ^ 2 + B * s) * D s) →
    (∀ s : ℂ, mellin k (s - 1) = Complex.exp (s ^ 2 + B * s) * Dd (1 - s)) →
    ∫ x, F x * h (δ x) ∂μ = ∫ x, F' x * k (δ' x) ∂μ'

theorem ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (z : ℂ) :
    (x : ℂ) ^ z = Complex.exp ((Real.log x : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), Complex.ofReal_log hx.le]

theorem rapidDecay_comp_mul_left {h : ℝ → ℂ} (hdec : RapidDecay h) {c : ℝ} (hc : 0 < c) :
    RapidDecay (fun t => h (c * t)) := by
  have := hdec.comp_mul_right hc
  simpa only [mul_comm] using this

theorem rapidDecay_const_mul {h : ℝ → ℂ} (hdec : RapidDecay h) (c : ℂ) :
    RapidDecay (fun t => c * h t) := by
  intro M
  obtain ⟨C, hC⟩ := hdec M
  refine ⟨‖c‖ * C, fun t ht => ?_⟩
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC t ht) (norm_nonneg c)

/-- The scaled pair: `t ↦ h(a t)` and `t ↦ a k(a⁻¹ t)` have Mellin transforms multiplied by
`a^s = exp((log a) s)`. Applying the pair identity to it gives Jacquet's identity (4.1),
`θ(a) = a θ'(a⁻¹)`. -/
theorem theta_eq_of_pairIdentity {X X' : Type*} [MeasurableSpace X] [MeasurableSpace X']
    {μ : Measure X} {μ' : Measure X'} {F : X → ℂ} {δ : X → ℝ} {F' : X' → ℂ} {δ' : X' → ℝ}
    {D Dd E : ℂ → ℂ} {sign : ℂ} (hpair : PairIdentity μ μ' F δ F' δ' D Dd E sign)
    {h k : ℝ → ℂ} (hh : Measurable h) (hk : Measurable k) (hhd : RapidDecay h)
    (hkd : RapidDecay k)
    (hhM : ∀ s : ℂ, mellin h (-s) = sign * E s * Complex.exp (s ^ 2) * D s)
    (hkM : ∀ s : ℂ, mellin k (s - 1) = Complex.exp (s ^ 2) * Dd (1 - s))
    {a : ℝ} (ha : 0 < a) :
    theta μ F δ h a = (a : ℂ) * theta μ' F' δ' k a⁻¹ := by
  have hai : 0 < a⁻¹ := inv_pos.mpr ha
  have key := hpair (Real.log a) (fun t => h (a * t)) (fun t => (a : ℂ) * k (a⁻¹ * t))
    (hh.comp (measurable_const.mul measurable_id))
    (measurable_const.mul (hk.comp (measurable_const.mul measurable_id)))
    (rapidDecay_comp_mul_left hhd ha) (rapidDecay_const_mul (rapidDecay_comp_mul_left hkd hai) _) (fun s => ?_) (fun s => ?_)
  · unfold theta
    rw [key, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  · rw [mellin_comp_mul_left h (-s) ha, neg_neg, smul_eq_mul, hhM s, ofReal_cpow_eq_exp ha,
      Complex.exp_add]
    ring
  · have h1 : mellin (fun t => (a : ℂ) * k (a⁻¹ * t)) (s - 1) =
        (a : ℂ) * mellin (fun t => k (a⁻¹ * t)) (s - 1) := by
      simpa only [smul_eq_mul] using mellin_const_smul (fun t => k (a⁻¹ * t)) (s - 1) (a : ℂ)
    rw [h1, mellin_comp_mul_left k (s - 1) hai, smul_eq_mul, hkM s, ofReal_cpow_eq_exp hai,
      Complex.exp_add]
    have ha' : (a : ℂ) = Complex.exp (Real.log a : ℂ) := by
      rw [← Complex.ofReal_exp, Real.exp_log ha]
    rw [ha', Real.log_inv]
    push_cast
    rw [show Complex.exp (Real.log a : ℂ) * (Complex.exp (-(Real.log a : ℂ) * -(s - 1)) *
        (Complex.exp (s ^ 2) * Dd (1 - s))) = Complex.exp ((Real.log a : ℂ) +
          -(Real.log a : ℂ) * -(s - 1)) * Complex.exp (s ^ 2) * Dd (1 - s) by
        rw [Complex.exp_add]; ring]
    rw [show (Real.log a : ℂ) + -(Real.log a : ℂ) * -(s - 1) = (Real.log a : ℂ) * s by ring]
    ring

/-! ### Continuation for kernels of the form `K(s) = K(0) δ^s` -/

theorem norm_kernel {X : Type*} {K : ℂ → X → ℂ} {δ : X → ℝ} (hδ : ∀ x, 0 < δ x)
    (hK : ∀ s x, K s x = K 0 x * (δ x : ℂ) ^ s) (σ : ℝ) (x : X) :
    ‖K (σ : ℂ) x‖ = ‖K 0 x‖ * δ x ^ σ := by
  rw [hK, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hδ x), Complex.ofReal_re]

theorem kernel_zero_eq {X : Type*} {K : ℂ → X → ℂ} {δ : X → ℝ} (hδ : ∀ x, 0 < δ x)
    (hK : ∀ s x, K s x = K 0 x * (δ x : ℂ) ^ s) (s : ℂ) (x : X) :
    K 0 x = K s x * (δ x : ℂ) ^ (-s) := by
  have hne : (δ x : ℂ) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast (hδ x).ne'))
  rw [hK s x, Complex.cpow_neg, mul_assoc, mul_inv_cancel₀ hne, mul_one]

/-- Continuation and functional equation for integrals of kernels `K(s) = K(0) δ^s` and
`Kd(s) = Kd(0) δ'^s` that converge on a right half-plane, from the pair identity for the real
pair factors. -/
theorem exists_continuation_of_kernels {X X' : Type*} [MeasurableSpace X] [MeasurableSpace X']
    (μ : Measure X) (μ' : Measure X') [SFinite μ] [SFinite μ']
    (K : ℂ → X → ℂ) (Kd : ℂ → X' → ℂ) (δ : X → ℝ) (δ' : X' → ℝ)
    (hδm : Measurable δ) (hδ'm : Measurable δ') (hδ : ∀ x, 0 < δ x) (hδ' : ∀ x, 0 < δ' x)
    (hK : ∀ s x, K s x = K 0 x * (δ x : ℂ) ^ s) (hKd : ∀ s x, Kd s x = Kd 0 x * (δ' x : ℂ) ^ s)
    (σ₀ : ℝ) (hKi : ∀ s : ℂ, σ₀ < s.re → Integrable (K s) μ)
    (hKdi : ∀ s : ℂ, σ₀ < s.re → Integrable (Kd s) μ')
    (Z Zd : ℂ → ℂ) (hZ : ∀ s : ℂ, σ₀ < s.re → Z s = ∫ x, K s x ∂μ)
    (hZd : ∀ s : ℂ, σ₀ < s.re → Zd s = ∫ x, Kd s x ∂μ')
    (ds es dds ees : List RealBlock) (b : ℝˣ) (c : NNReal) (hc : 0 < c) (sign : ℂ)
    (hsign : sign ≠ 0)
    (hpair : PairIdentity μ μ' (K 0) δ (Kd 0) δ' (realPairLFactor ds es).denominator
      (realPairLFactor dds ees).denominator (fun s => (realPairEpsilon ds es b c hc s : ℂ)) sign) :
    ∃ (σ : ℝ) (M Md : ℂ → ℂ),
      MeromorphicOn M univ ∧ MeromorphicOn Md univ ∧
      (∀ s : ℂ, σ < s.re → Z s = M s) ∧
      (∀ s : ℂ, σ < s.re → Zd s = Md s) ∧
      ∀ᶠ s in codiscrete ℂ,
        ((realPairLFactor ds es).denominator s)⁻¹ * Md (1 - s) =
          sign * (realPairEpsilon ds es b c hc s : ℂ) *
            ((realPairLFactor dds ees).denominator (1 - s))⁻¹ * M s := by
  obtain ⟨σ₁, h, k, hhm, hkm, hhd, hkd, hhM, hkM, hh0, hk0, hfac⟩ :=
    realPairMellinFactor ds es dds ees b c hc sign hsign
  set N : ℝ := σ₀ + 1 with hN
  have hNre : σ₀ < ((N : ℝ) : ℂ).re := by simp [hN]
  have hF : AEStronglyMeasurable (K 0) μ := by
    have hm : Measurable fun x => (δ x : ℂ) ^ (-((N : ℝ) : ℂ)) :=
      (Complex.measurable_ofReal.comp hδm).pow_const _
    have := (hKi _ hNre).aestronglyMeasurable.mul hm.aestronglyMeasurable
    exact this.congr (Eventually.of_forall fun x => (kernel_zero_eq hδ hK _ x).symm)
  have hF' : AEStronglyMeasurable (Kd 0) μ' := by
    have hm : Measurable fun x => (δ' x : ℂ) ^ (-((N : ℝ) : ℂ)) :=
      (Complex.measurable_ofReal.comp hδ'm).pow_const _
    have := (hKdi _ hNre).aestronglyMeasurable.mul hm.aestronglyMeasurable
    exact this.congr (Eventually.of_forall fun x => (kernel_zero_eq hδ' hKd _ x).symm)
  have hFN : ∀ σ : ℝ, N ≤ σ → Integrable (fun x => ‖K 0 x‖ * δ x ^ σ) μ := by
    intro σ hσ
    have hlt : σ₀ < ((σ : ℝ) : ℂ).re := by simp only [Complex.ofReal_re]; linarith
    exact (hKi _ hlt).norm.congr (Eventually.of_forall fun x => norm_kernel hδ hK σ x)
  have hF'N : ∀ σ : ℝ, N ≤ σ → Integrable (fun x => ‖Kd 0 x‖ * δ' x ^ σ) μ' := by
    intro σ hσ
    have hlt : σ₀ < ((σ : ℝ) : ℂ).re := by simp only [Complex.ofReal_re]; linarith
    exact (hKdi _ hlt).norm.congr (Eventually.of_forall fun x => norm_kernel hδ' hKd σ x)
  have hZ' : ∀ s : ℂ, N ≤ s.re → Z s = ∫ x, K 0 x * (δ x : ℂ) ^ s ∂μ := by
    intro s hs
    rw [hZ s (by linarith)]
    exact integral_congr_ae (Eventually.of_forall fun x => hK s x)
  have hZd' : ∀ s : ℂ, N ≤ s.re → Zd s = ∫ x, Kd 0 x * (δ' x : ℂ) ^ s ∂μ' := by
    intro s hs
    rw [hZd s (by linarith)]
    exact integral_congr_ae (Eventually.of_forall fun x => hKd s x)
  have htheta : ∀ a : ℝ, 0 < a →
      theta μ (K 0) δ h a = (a : ℂ) * theta μ' (Kd 0) δ' k a⁻¹ :=
    fun a ha => theta_eq_of_pairIdentity hpair hhm hkm hhd hkd hhM hkM ha
  exact exists_continuation μ μ' (K 0) δ (Kd 0) δ' hF hF' hδm hδ'm hδ hδ' h k hhm hkm hhd hkd
    N hFN hF'N htheta σ₁ hh0 hk0 Z Zd (fun s => ((realPairLFactor ds es).denominator s)⁻¹)
    (fun s => ((realPairLFactor dds ees).denominator s)⁻¹)
    (fun s => (realPairEpsilon ds es b c hc s : ℂ)) sign hZ' hZd' hfac

/-! ### The real Rankin–Selberg integrals -/

local instance realPairIdGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
local instance realPairIdGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
local instance realPairIdNMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
local instance realPairIdNBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := ⟨rfl⟩
local instance realPairIdQMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
local instance realPairIdQBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

/-- `|det g|` at the representative `g` of a class in `N_(r+1)(ℝ) \ GL_(r+1)(ℝ)`. -/
def quotientDetAbs {r : ℕ} (q : LeftUnipotentQuotient r ℝ) : ℝ :=
  realNormalizedAbs (Matrix.det q.out.val)

theorem detAbs_pos {r : ℕ} (g : Langlands.GeneralLinear (r + 1) ℝ) :
    0 < realNormalizedAbs (Matrix.det g.val) :=
  abs_pos.mpr (Matrix.isUnit_iff_isUnit_det _ |>.mp g.isUnit).ne_zero

theorem quotientDetAbs_pos {r : ℕ} (q : LeftUnipotentQuotient r ℝ) : 0 < quotientDetAbs q :=
  detAbs_pos q.out

theorem continuous_quotientDetAbs {r : ℕ} : Continuous (quotientDetAbs (r := r)) := by
  let f : Langlands.GeneralLinear (r + 1) ℝ → ℝ := fun g => realNormalizedAbs (Matrix.det g.val)
  have hinv : ∀ u : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g,
      f (u.val * g) = f g := by
    intro u g
    show realNormalizedAbs (Matrix.det (u.val * g).val) = realNormalizedAbs (Matrix.det g.val)
    rw [Units.val_mul, Matrix.det_mul, Langlands.RankinSelberg.unipotent_det, one_mul]
  have hc : Continuous f :=
    continuous_abs.comp ((continuous_id.matrix_det).comp Units.continuous_val)
  have h : quotientDetAbs (r := r) =
      Langlands.QuotientIntegration.descend (Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ)
        f hinv :=
    funext fun q => RealEqualConvergence.out_eq_descend f hinv q
  rw [h]
  exact RealEqualConvergence.continuous_descend_real hinv hc

theorem measurable_quotientDetAbs {r : ℕ} : Measurable (quotientDetAbs (r := r)) :=
  continuous_quotientDetAbs.measurable

theorem detPower_eq_cpow {r : ℕ} (g : Langlands.GeneralLinear (r + 1) ℝ) (s : ℂ) :
    ArchimedeanLocal.detPower realNormalizedAbs g s =
      ((realNormalizedAbs (Matrix.det g.val) : ℝ) : ℂ) ^ s := by
  rw [ofReal_cpow_eq_exp (detAbs_pos g), ArchimedeanLocal.detPower, mul_comm]

/-- The quotient `N_(r+1)(ℝ) \ GL_(r+1)(ℝ)` is σ-compact: it is the continuous image of
`ℝ^(r+1) × O(r+1)` under `(y, k) ↦ [torus(y) k]`. -/
theorem sigmaCompactSpace_quotient (r : ℕ) : SigmaCompactSpace (LeftUnipotentQuotient r ℝ) := by
  rw [← isSigmaCompact_univ_iff]
  have h := RealIwasawa.alphaQ_preimage (n := r + 1) Set.univ
  rw [Set.preimage_univ, Set.univ_prod_univ, Set.image_univ] at h
  rw [h]
  exact isSigmaCompact_range RealIwasawa.continuous_mk_torus_mul

/-- A compatible quotient measure is σ-finite: it is finite on compact sets (regularity) and
the quotient is σ-compact. -/
theorem sigmaFinite_measure {r : ℕ} (D : RealQuotientMeasureData r) : SigmaFinite D.measure := by
  have := sigmaCompactSpace_quotient r
  have := D.unipotentHaar_rightInvariant
  have := D.compatible.regular
  infer_instance

theorem sigmaFinite_haar (ν : Langlands.HarmonicAnalysis.AdditiveHaarMeasure ℝ) :
    SigmaFinite ν.measure :=
  RealUnequalDualConvergence.sigmaFinite_haar ν

theorem sigmaFinite_rect (ν : Langlands.HarmonicAnalysis.AdditiveHaarMeasure ℝ) (d a : ℕ) :
    SigmaFinite (rectangularMeasure ν d a) :=
  RealUnequalDualConvergence.sigmaFinite_rect ν d a

theorem sFinite_dualMeasure {r t : ℕ} (a : ℝˣ) (D : RealQuotientMeasureData t) :
    SFinite (realUnequalDualMeasure (r := r) a D) := by
  have := sigmaFinite_measure D
  have := sigmaFinite_rect (realSelfDualMeasure a) (r - (t + 1)) (t + 1)
  unfold realUnequalDualMeasure
  infer_instance

theorem realEqualIntegrand_eq_mul {r : ℕ} (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (Φ : (Fin (r + 1) → ℝ) → ℂ) (s : ℂ) (q : LeftUnipotentQuotient r ℝ) :
    realEqualIntegrand W W' Φ s q =
      realEqualIntegrand W W' Φ 0 q * (quotientDetAbs q : ℂ) ^ s := by
  simp only [realEqualIntegrand, equalIntegrand, detPower_eq_cpow, Complex.cpow_zero, mul_one,
    quotientDetAbs]

theorem realUnequalIntegrand_eq_mul {r t : ℕ} (h : t < r)
    (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ)
    (s : ℂ) (q : LeftUnipotentQuotient t ℝ) :
    realUnequalIntegrand h W W' s q =
      realUnequalIntegrand h W W' 0 q * (quotientDetAbs q : ℂ) ^ s := by
  have hx : ((realNormalizedAbs (Matrix.det q.out.val) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (detAbs_pos q.out).ne'
  simp only [realUnequalIntegrand, ArchimedeanLocal.unequalIntegrand, detPower_eq_cpow,
    quotientDetAbs]
  rw [show s - ((r - t : ℕ) : ℂ) / 2 = (0 - ((r - t : ℕ) : ℂ) / 2) + s by ring,
    Complex.cpow_add _ _ hx]
  ring

theorem realUnequalDualKernel_eq_mul {r t : ℕ} (h : t < r)
    (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ)
    (s : ℂ) (p : LeftUnipotentQuotient t ℝ × Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℝ) :
    realUnequalDualKernel h W W' s p =
      realUnequalDualKernel h W W' 0 p * (quotientDetAbs p.1 : ℂ) ^ s := by
  have hx : ((realNormalizedAbs (Matrix.det p.1.out.val) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (detAbs_pos p.1.out).ne'
  simp only [realUnequalDualKernel, blockKernel, detPower_eq_cpow, quotientDetAbs]
  rw [show s - ((r - t : ℕ) : ℂ) / 2 = (0 - ((r - t : ℕ) : ℂ) / 2) + s by ring,
    Complex.cpow_add _ _ hx]
  ring

/-- The pair identity for the unequal-rank integrals `Ψ(s; W, W')` and
`Ψ_(n-m-1)(s; ρ(w_(n,m)) W̃, W̃')` (Jacquet 2009, p. 54 and Theorem 2.1(iii)), with the
`L`- and `ε`-factors of `RealJacquet.UnequalEquation`. -/
def UnequalPairIdentity {r t : ℕ} (h : t < r) (a : ℝˣ) (D : RealQuotientMeasureData t)
    (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ)
    (ds es dds ees : List RealBlock) (b : ℝˣ) (sign : ℂ) : Prop :=
  PairIdentity D.measure (realUnequalDualMeasure (r := r) a D)
    (realUnequalIntegrand h W W' 0) quotientDetAbs
    (realUnequalDualKernel h W W' 0) (fun p => quotientDetAbs p.1)
    (realPairLFactor ds es).denominator (realPairLFactor dds ees).denominator
    (fun s => (realPairEpsilon ds es b (NNReal.sqrt ‖(a : ℝ)‖₊)
      (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) s : ℂ)) sign

/-- The pair identity for the equal-rank integrals `Ψ(s; W, W', Φ)` and `Ψ(s; W̃, W̃', Φ̂)`
(Jacquet 2009, p. 53), with the `L`- and `ε`-factors of `RealJacquet.EqualEquation`. -/
def EqualPairIdentity {r : ℕ} (a b : ℝˣ) (D : RealQuotientMeasureData r)
    (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ)
    (ds es dds ees : List RealBlock) (sign : ℂ) : Prop :=
  PairIdentity D.measure D.measure (realEqualIntegrand W W' Φ 0) quotientDetAbs
    (realEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
      (ArchimedeanLocal.dualFunction (r + 1) W') (realFourierTransform b Φ) 0) quotientDetAbs
    (realPairLFactor ds es).denominator (realPairLFactor dds ees).denominator
    (fun s => (realPairEpsilon ds es b (NNReal.sqrt ‖(a : ℝ)‖₊)
      (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) s : ℂ)) sign

end Langlands.Global.RankinSelbergGlobal.ArchimedeanRealPairIdentity

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.LocalFactor.Archimedean ArchimedeanMellinPair ArchimedeanLocal
  ArchimedeanRealPairIdentity
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure)

local instance realPairIdGLMeasurable' (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
local instance realPairIdGLBorel' (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
local instance realPairIdNMeasurable' (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
local instance realPairIdNBorel' (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := ⟨rfl⟩
local instance realPairIdQMeasurable' (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
local instance realPairIdQBorel' (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

/-- Continuation and functional equation of the real local Rankin–Selberg integrals, in both
ranks, from Jacquet's pair identity: if the integrals converge absolutely on a right
half-plane and satisfy the pair identity for the real pair factors, they have meromorphic
continuations satisfying the multiplied-out functional equation, with the integrals,
`L`-factors and `ε`-factor of `RealJacquet.UnequalEquation` and `RealJacquet.EqualEquation`. -/
def RealPairIdentityContinuationStatement : Prop :=
  (∀ (r t : ℕ) (h : t < r) (a b : ℝˣ) (D : RealQuotientMeasureData t)
      (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ)
      (ds es dds ees : List RealBlock) (sign : ℂ) (σ₀ : ℝ),
      sign ≠ 0 →
      (∀ s : ℂ, σ₀ < s.re → Integrable (realUnequalIntegrand h W W' s) D.measure) →
      (∀ s : ℂ, σ₀ < s.re →
        Integrable (realUnequalDualKernel h W W' s) (realUnequalDualMeasure (r := r) a D)) →
      UnequalPairIdentity h a D W W' ds es dds ees b sign →
      ∃ (σ : ℝ) (M Md : ℂ → ℂ),
        MeromorphicOn M Set.univ ∧ MeromorphicOn Md Set.univ ∧
        (∀ s : ℂ, σ < s.re → realUnequalIntegral h D W W' s = M s) ∧
        (∀ s : ℂ, σ < s.re → realUnequalDualIntegral h a D W W' s = Md s) ∧
        ∀ᶠ s in Filter.codiscrete ℂ,
          ((realPairLFactor ds es).denominator s)⁻¹ * Md (1 - s) =
            sign * (realPairEpsilon ds es b (NNReal.sqrt ‖(a : ℝ)‖₊)
              (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) s : ℂ) *
              ((realPairLFactor dds ees).denominator (1 - s))⁻¹ * M s) ∧
  (∀ (r : ℕ) (a b : ℝˣ) (D : RealQuotientMeasureData r)
      (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ)
      (ds es dds ees : List RealBlock) (sign : ℂ) (σ₀ : ℝ),
      sign ≠ 0 →
      (∀ s : ℂ, σ₀ < s.re → Integrable (realEqualIntegrand W W' Φ s) D.measure) →
      (∀ s : ℂ, σ₀ < s.re →
        Integrable (realEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
          (ArchimedeanLocal.dualFunction (r + 1) W') (realFourierTransform b Φ) s) D.measure) →
      EqualPairIdentity a b D W W' Φ ds es dds ees sign →
      ∃ (σ : ℝ) (M Md : ℂ → ℂ),
        MeromorphicOn M Set.univ ∧ MeromorphicOn Md Set.univ ∧
        (∀ s : ℂ, σ < s.re → realEqualIntegral D W W' Φ s = M s) ∧
        (∀ s : ℂ, σ < s.re → realEqualDualIntegral b D W W' Φ s = Md s) ∧
        ∀ᶠ s in Filter.codiscrete ℂ,
          ((realPairLFactor ds es).denominator s)⁻¹ * Md (1 - s) =
            sign * (realPairEpsilon ds es b (NNReal.sqrt ‖(a : ℝ)‖₊)
              (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) s : ℂ) *
              ((realPairLFactor dds ees).denominator (1 - s))⁻¹ * M s)

theorem realPairIdentityContinuation : RealPairIdentityContinuationStatement := by
  refine ⟨?_, ?_⟩
  · intro r t h a b D W W' ds es dds ees sign σ₀ hsign hK hKd hpair
    have := sigmaFinite_measure D
    have := sFinite_dualMeasure (r := r) a D
    exact exists_continuation_of_kernels D.measure (realUnequalDualMeasure (r := r) a D)
      (realUnequalIntegrand h W W') (realUnequalDualKernel h W W') quotientDetAbs
      (fun p => quotientDetAbs p.1) measurable_quotientDetAbs
      (measurable_quotientDetAbs.comp measurable_fst) quotientDetAbs_pos
      (fun p => quotientDetAbs_pos p.1) (realUnequalIntegrand_eq_mul h W W')
      (realUnequalDualKernel_eq_mul h W W') σ₀ hK hKd _ _ (fun s _ => rfl)
      (fun s hs => by
        rw [show realUnequalDualMeasure (r := r) a D = D.measure.prod
            (rectangularMeasure (realSelfDualMeasure a) (r - (t + 1)) (t + 1)) from rfl,
          integral_prod _ (hKd s hs)]
        rfl)
      ds es dds ees b _ _ sign hsign hpair
  · intro r a b D W W' Φ ds es dds ees sign σ₀ hsign hK hKd hpair
    have := sigmaFinite_measure D
    exact exists_continuation_of_kernels D.measure D.measure
      (realEqualIntegrand W W' Φ)
      (realEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
        (ArchimedeanLocal.dualFunction (r + 1) W') (realFourierTransform b Φ))
      quotientDetAbs quotientDetAbs measurable_quotientDetAbs measurable_quotientDetAbs
      quotientDetAbs_pos quotientDetAbs_pos (realEqualIntegrand_eq_mul W W' Φ)
      (realEqualIntegrand_eq_mul _ _ _) σ₀ hK hKd _ _ (fun s _ => rfl) (fun s _ => rfl)
      ds es dds ees b _ _ sign hsign hpair

end Langlands.Global.RankinSelbergGlobal
