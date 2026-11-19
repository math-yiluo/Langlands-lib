import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Analytic.Order

/-!
# Continuation from a Mellin pair identity (core of Jacquet 2009, Proposition 4.1)

See the paired Markdown file.
-/

universe u v

open MeasureTheory Set Filter Asymptotics
open scoped Topology

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanMellinPair

/-- Rapid decay on `(0, ∞)`: for every real `M` there is `C` with `‖h t‖ ≤ C t ^ M` for all
`t > 0`. -/
def RapidDecay (h : ℝ → ℂ) : Prop :=
  ∀ M : ℝ, ∃ C : ℝ, ∀ t : ℝ, 0 < t → ‖h t‖ ≤ C * t ^ M

theorem RapidDecay.comp_mul_right {h : ℝ → ℂ} (hdec : RapidDecay h) {c : ℝ} (hc : 0 < c) :
    RapidDecay (fun t => h (t * c)) := by
  intro M
  obtain ⟨C, hC⟩ := hdec M
  refine ⟨C * c ^ M, fun t ht => ?_⟩
  have := hC (t * c) (mul_pos ht hc)
  rw [Real.mul_rpow ht.le hc.le] at this
  calc ‖h (t * c)‖ ≤ C * (t ^ M * c ^ M) := this
    _ = C * c ^ M * t ^ M := by ring

theorem RapidDecay.nonneg_const {h : ℝ → ℂ} {M C : ℝ}
    (hC : ∀ t : ℝ, 0 < t → ‖h t‖ ≤ C * t ^ M) : 0 ≤ C := by
  have := hC 1 one_pos
  rw [Real.one_rpow, mul_one] at this
  exact (norm_nonneg _).trans this

/-- A measurable rapidly decreasing function is integrable against every power of `t` on
`(0, ∞)`. -/
theorem RapidDecay.integrableOn {h : ℝ → ℂ} (hdec : RapidDecay h) (hm : Measurable h)
    (σ : ℝ) : IntegrableOn (fun t : ℝ => t ^ σ * ‖h t‖) (Ioi 0) := by
  obtain ⟨C₁, hC₁⟩ := hdec (-σ)
  obtain ⟨C₂, hC₂⟩ := hdec (-σ - 2)
  have hmeas : Measurable (fun t : ℝ => t ^ σ * ‖h t‖) :=
    (measurable_id.pow_const σ).mul hm.norm
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
  refine IntegrableOn.union ?_ ?_
  · refine Measure.integrableOn_of_bounded (M := C₁) (by simp) hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := ht.1
    have hpos : 0 < t ^ σ := Real.rpow_pos_of_pos ht0 σ
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hpos.le (norm_nonneg _))]
    calc t ^ σ * ‖h t‖ ≤ t ^ σ * (C₁ * t ^ (-σ)) :=
          mul_le_mul_of_nonneg_left (hC₁ t ht0) hpos.le
      _ = C₁ * (t ^ σ * t ^ (-σ)) := by ring
      _ = C₁ := by rw [← Real.rpow_add ht0, add_neg_cancel, Real.rpow_zero, mul_one]
  · have hint : IntegrableOn (fun t : ℝ => C₂ * t ^ (-2 : ℝ)) (Ioi 1) :=
      ((integrableOn_Ioi_rpow_iff one_pos).2 (by norm_num)).const_mul C₂
    refine hint.mono' hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := lt_trans one_pos ht
    have hpos : 0 < t ^ σ := Real.rpow_pos_of_pos ht0 σ
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hpos.le (norm_nonneg _))]
    calc t ^ σ * ‖h t‖ ≤ t ^ σ * (C₂ * t ^ (-σ - 2)) :=
          mul_le_mul_of_nonneg_left (hC₂ t ht0) hpos.le
      _ = C₂ * (t ^ σ * t ^ (-σ - 2)) := by ring
      _ = C₂ * t ^ (-2 : ℝ) := by rw [← Real.rpow_add ht0]; ring_nf

/-- A measurable rapidly decreasing function is Mellin convergent at every `s`. -/
theorem RapidDecay.mellinConvergent {h : ℝ → ℂ} (hdec : RapidDecay h) (hm : Measurable h)
    (s : ℂ) : MellinConvergent h s := by
  rw [MellinConvergent, mellin_convergent_iff_norm (subset_refl _) measurableSet_Ioi
    hm.aestronglyMeasurable]
  exact hdec.integrableOn hm (s.re - 1)

/-- Scaling of the weighted `L¹` norm of a function on `(0, ∞)`. -/
theorem integral_rpow_mul_norm_comp_mul_right (h : ℝ → ℂ) (σ : ℝ) {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), t ^ (-σ - 1) * ‖h (t * c)‖ =
      c ^ σ * ∫ t in Ioi (0 : ℝ), t ^ (-σ - 1) * ‖h t‖ := by
  have hcongr : ∀ t ∈ Ioi (0 : ℝ), t ^ (-σ - 1) * ‖h (t * c)‖ =
      c ^ (σ + 1) * ((t * c) ^ (-σ - 1) * ‖h (t * c)‖) := by
    intro t ht
    rw [Real.mul_rpow (le_of_lt ht) hc.le]
    have : c ^ (σ + 1) * c ^ (-σ - 1) = 1 := by
      rw [← Real.rpow_add hc]; ring_nf; exact Real.rpow_zero c
    calc t ^ (-σ - 1) * ‖h (t * c)‖
        = (c ^ (σ + 1) * c ^ (-σ - 1)) * (t ^ (-σ - 1) * ‖h (t * c)‖) := by rw [this, one_mul]
      _ = _ := by ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
    integral_comp_mul_right_Ioi (fun t => t ^ (-σ - 1) * ‖h t‖) 0 hc, zero_mul, smul_eq_mul,
    ← mul_assoc]
  congr 1
  rw [Real.rpow_add hc, Real.rpow_one, mul_assoc, mul_inv_cancel₀ hc.ne', mul_one]

/-- The pointwise bound for the theta function. -/
theorem norm_integral_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : X → ℂ) (δ : X → ℝ) (hδ : ∀ x, 0 < δ x) (h : ℝ → ℂ) {M C : ℝ}
    (hC : ∀ t : ℝ, 0 < t → ‖h t‖ ≤ C * t ^ M)
    (hint : Integrable (fun x => ‖F x‖ * δ x ^ M) μ) {a : ℝ} (ha : 0 < a) :
    ‖∫ x, F x * h (a * δ x) ∂μ‖ ≤ C * a ^ M * ∫ x, ‖F x‖ * δ x ^ M ∂μ := by
  calc ‖∫ x, F x * h (a * δ x) ∂μ‖ ≤ ∫ x, C * a ^ M * (‖F x‖ * δ x ^ M) ∂μ := by
        refine norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall fun x => ?_)
        rw [norm_mul]
        have := hC (a * δ x) (mul_pos ha (hδ x))
        rw [Real.mul_rpow ha.le (hδ x).le] at this
        calc ‖F x‖ * ‖h (a * δ x)‖ ≤ ‖F x‖ * (C * (a ^ M * δ x ^ M)) :=
              mul_le_mul_of_nonneg_left this (norm_nonneg _)
          _ = C * a ^ M * (‖F x‖ * δ x ^ M) := by ring
    _ = C * a ^ M * ∫ x, ‖F x‖ * δ x ^ M ∂μ := integral_const_mul _ _

/-- The theta function `a ↦ ∫ F(x) h(a δ(x)) dμ(x)` is a.e. strongly measurable. -/
theorem aestronglyMeasurable_theta {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    (F : X → ℂ) (δ : X → ℝ) (hF : AEStronglyMeasurable F μ) (hδm : Measurable δ)
    (h : ℝ → ℂ) (hh : Measurable h) (ρ : Measure ℝ) [SFinite ρ] :
    AEStronglyMeasurable (fun a : ℝ => ∫ x, F x * h (a * δ x) ∂μ) ρ := by
  have : AEStronglyMeasurable (fun p : ℝ × X => F p.2 * h (p.1 * δ p.2)) (ρ.prod μ) :=
    hF.comp_snd.mul (hh.comp (measurable_fst.mul (hδm.comp measurable_snd))).aestronglyMeasurable
  exact this.integral_prod_right'

/-- The theta function `a ↦ ∫ F(x) h(a δ(x)) dμ(x)` (Jacquet's `θ(a)`, p.24). -/
noncomputable def theta {X : Type*} [MeasurableSpace X] (μ : Measure X) (F : X → ℂ)
    (δ : X → ℝ) (h : ℝ → ℂ) (a : ℝ) : ℂ :=
  ∫ x, F x * h (a * δ x) ∂μ

/-- One-sided Mellin computation: for `Re s` in the convergence range of `F`, the Mellin
transform of the theta function at `-s` factors. -/
theorem mellin_theta {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    (F : X → ℂ) (δ : X → ℝ) (hF : AEStronglyMeasurable F μ) (hδm : Measurable δ)
    (hδ : ∀ x, 0 < δ x) (h : ℝ → ℂ) (hh : Measurable h) (hdec : RapidDecay h) (s : ℂ)
    (hint : Integrable (fun x => ‖F x‖ * δ x ^ s.re) μ) :
    mellin (theta μ F δ h) (-s) = (∫ x, F x * (δ x : ℂ) ^ s ∂μ) * mellin h (-s) := by
  show mellin (fun a => ∫ x, F x * h (a * δ x) ∂μ) (-s) = _
  set ρ : Measure ℝ := volume.restrict (Ioi 0) with hρ
  let G : ℝ → X → ℂ := fun a x => (a : ℂ) ^ (-s - 1) * (F x * h (a * δ x))
  have hGm : AEStronglyMeasurable (Function.uncurry G) (ρ.prod μ) := by
    have h1 : Measurable (fun p : ℝ × X => (p.1 : ℂ) ^ (-s - 1)) :=
      (Complex.measurable_ofReal.comp measurable_fst).pow_const _
    exact h1.aestronglyMeasurable.mul (hF.comp_snd.mul
      (hh.comp (measurable_fst.mul (hδm.comp measurable_snd))).aestronglyMeasurable)
  -- the inner integral in `a`, for fixed `x`
  have hinner : ∀ x, ∫ a in Ioi (0 : ℝ), G a x =
      F x * ((δ x : ℂ) ^ s * mellin h (-s)) := by
    intro x
    have hc := mellin_comp_mul_right h (-s) (hδ x)
    rw [neg_neg, smul_eq_mul] at hc
    rw [← hc, mellin, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun a _ => ?_
    simp only [G, smul_eq_mul, mul_comm (a : ℝ) (δ x)]
    ring
  have hnorm : ∀ x, ∫ a in Ioi (0 : ℝ), ‖G a x‖ =
      ‖F x‖ * δ x ^ s.re * ∫ t in Ioi (0 : ℝ), t ^ (-s.re - 1) * ‖h t‖ := by
    intro x
    have hcongr : ∀ a ∈ Ioi (0 : ℝ), ‖G a x‖ = ‖F x‖ * (a ^ (-s.re - 1) * ‖h (a * δ x)‖) := by
      intro a ha
      simp only [G, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ha, Complex.sub_re,
        Complex.neg_re, Complex.one_re]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
      integral_rpow_mul_norm_comp_mul_right h s.re (hδ x)]
    ring
  have hGint : Integrable (Function.uncurry G) (ρ.prod μ) := by
    refine (integrable_prod_iff' hGm).2 ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · have hconv := (hdec.comp_mul_right (hδ x)).mellinConvergent
        (hh.comp (measurable_id.mul_const (δ x))) (-s)
      have := hconv.const_mul (F x)
      refine this.congr (Eventually.of_forall fun a => ?_)
      simp only [G, Function.uncurry, smul_eq_mul]
      ring
    · simp only [Function.uncurry_apply_pair]
      refine (hint.mul_const (∫ t in Ioi (0 : ℝ), t ^ (-s.re - 1) * ‖h t‖)).congr
        (Eventually.of_forall fun x => ?_)
      exact (hnorm x).symm
  have hswap := integral_integral_swap hGint
  calc mellin (fun a => ∫ x, F x * h (a * δ x) ∂μ) (-s)
      = ∫ a in Ioi (0 : ℝ), ∫ x, G a x ∂μ := by
        rw [mellin]
        refine setIntegral_congr_fun measurableSet_Ioi fun a _ => ?_
        rw [smul_eq_mul, ← integral_const_mul]
    _ = ∫ x, (∫ a in Ioi (0 : ℝ), G a x) ∂μ := hswap
    _ = ∫ x, F x * (δ x : ℂ) ^ s * mellin h (-s) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [hinner x]
        ring
    _ = (∫ x, F x * (δ x : ℂ) ^ s ∂μ) * mellin h (-s) := integral_mul_const _ _

/-- A rapidly decreasing function is `O(t ^ M)` along any filter on which `t > 0` eventually. -/
theorem RapidDecay.isBigO {g : ℝ → ℂ} (hdec : RapidDecay g) {l : Filter ℝ}
    (hl : ∀ᶠ t in l, 0 < t) (M : ℝ) : g =O[l] (fun t => t ^ M) := by
  obtain ⟨C, hC⟩ := hdec M
  refine IsBigO.of_bound C ?_
  filter_upwards [hl] with t ht
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht M)]
  exact hC t ht

/-- The Mellin transform of a rapidly decreasing a.e. strongly measurable function is entire. -/
theorem RapidDecay.differentiable_mellin {g : ℝ → ℂ} (hdec : RapidDecay g)
    (hm : AEStronglyMeasurable g volume) : Differentiable ℂ (mellin g) := by
  intro s
  obtain ⟨C, hC⟩ := hdec 0
  have hloc : LocallyIntegrableOn g (Ioi 0) := by
    rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
    intro K hK hKc
    refine Measure.integrableOn_of_bounded (M := C) hKc.measure_lt_top.ne hm ?_
    refine (ae_restrict_iff' hKc.measurableSet).2 (Eventually.of_forall fun t ht => ?_)
    simpa using hC t (hK ht)
  have hbot : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  exact mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1) hloc
    (hdec.isBigO (eventually_gt_atTop 0) _) (by linarith)
    (hdec.isBigO hbot _) (by linarith)

/-- Separate bounds near `0` and near `∞` give rapid decay. -/
theorem rapidDecay_of_bounds {g : ℝ → ℂ}
    (h0 : ∀ M : ℝ, ∃ C : ℝ, ∀ a : ℝ, 0 < a → a ≤ 1 → ‖g a‖ ≤ C * a ^ M)
    (h1 : ∀ M : ℝ, ∃ C : ℝ, ∀ a : ℝ, 1 ≤ a → ‖g a‖ ≤ C * a ^ M) : RapidDecay g := by
  intro M
  obtain ⟨C₀, hC₀⟩ := h0 M
  obtain ⟨C₁, hC₁⟩ := h1 M
  refine ⟨max C₀ C₁, fun a ha => ?_⟩
  have hp : 0 ≤ a ^ M := (Real.rpow_pos_of_pos ha M).le
  rcases le_total a 1 with h | h
  · exact (hC₀ a ha h).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)
  · exact (hC₁ a h).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp)

/-- The bound `‖θ(a)‖ ≤ C a ^ M` whenever `‖F‖ δ ^ M` is integrable. -/
theorem theta_bound {X : Type*} [MeasurableSpace X] (μ : Measure X) (F : X → ℂ) (δ : X → ℝ)
    (hδ : ∀ x, 0 < δ x) {h : ℝ → ℂ} (hdec : RapidDecay h) {M : ℝ}
    (hint : Integrable (fun x => ‖F x‖ * δ x ^ M) μ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 < a → ‖theta μ F δ h a‖ ≤ C * a ^ M := by
  obtain ⟨C, hC⟩ := hdec M
  have hC0 := RapidDecay.nonneg_const hC
  have hI : 0 ≤ ∫ x, ‖F x‖ * δ x ^ M ∂μ :=
    integral_nonneg fun x => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hδ x).le M)
  refine ⟨C * ∫ x, ‖F x‖ * δ x ^ M ∂μ, mul_nonneg hC0 hI, fun a ha => ?_⟩
  calc ‖theta μ F δ h a‖ ≤ C * a ^ M * ∫ x, ‖F x‖ * δ x ^ M ∂μ :=
        norm_integral_le μ F δ hδ h hC hint ha
    _ = _ := by ring

/-- Under the pair identity (Jacquet's (4.1)) the theta function decreases rapidly at both
ends. -/
theorem theta_rapidDecay {X X' : Type*} [MeasurableSpace X] [MeasurableSpace X']
    (μ : Measure X) (μ' : Measure X') (F : X → ℂ) (δ : X → ℝ) (F' : X' → ℂ) (δ' : X' → ℝ)
    (hδ : ∀ x, 0 < δ x) (hδ' : ∀ x, 0 < δ' x) {h k : ℝ → ℂ} (hhd : RapidDecay h)
    (hkd : RapidDecay k) {N : ℝ}
    (hFN : ∀ σ : ℝ, N ≤ σ → Integrable (fun x => ‖F x‖ * δ x ^ σ) μ)
    (hF'N : ∀ σ : ℝ, N ≤ σ → Integrable (fun x => ‖F' x‖ * δ' x ^ σ) μ')
    (hpair : ∀ a : ℝ, 0 < a → theta μ F δ h a = (a : ℂ) * theta μ' F' δ' k a⁻¹) :
    RapidDecay (theta μ F δ h) := by
  refine rapidDecay_of_bounds (fun M => ?_) (fun M => ?_)
  · obtain ⟨C, hC0, hC⟩ := theta_bound μ F δ hδ hhd (hFN (max N M) (le_max_left _ _))
    refine ⟨C, fun a ha ha1 => (hC a ha).trans ?_⟩
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge ha ha1 (le_max_right _ _)) hC0
  · obtain ⟨C, hC0, hC⟩ :=
      theta_bound μ' F' δ' hδ' hkd (hF'N (max N (1 - M)) (le_max_left _ _))
    refine ⟨C, fun a ha1 => ?_⟩
    have ha : 0 < a := lt_of_lt_of_le one_pos ha1
    rw [hpair a ha, norm_mul, Complex.norm_of_nonneg ha.le]
    calc a * ‖theta μ' F' δ' k a⁻¹‖ ≤ a * (C * a⁻¹ ^ max N (1 - M)) :=
          mul_le_mul_of_nonneg_left (hC a⁻¹ (inv_pos.2 ha)) ha.le
      _ = C * a ^ (1 - max N (1 - M)) := by
          rw [Real.inv_rpow ha.le, Real.rpow_sub ha, Real.rpow_one]
          ring
      _ ≤ C * a ^ M := by
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ha1 ?_) hC0
          have := le_max_right N (1 - M)
          linarith

/-- The core of Jacquet 2009, Proposition 4.1 (pp.23-25). Under the pair identity
`θ(a) = a θ'(a⁻¹)`, the function `s ↦ ∫ θ(a) a ^ (-s) d^×a` is entire. It equals
`(∫ F δ ^ s) · ∫ h(a) a ^ (-s) d^×a` for `Re s ≥ N` and
`(∫ F' δ' ^ (1 - s)) · ∫ k(a) a ^ (s - 1) d^×a` for `Re s ≤ 1 - N`. -/
theorem mellin_theta_entire {X X' : Type*} [MeasurableSpace X] [MeasurableSpace X']
    (μ : Measure X) (μ' : Measure X') [SFinite μ] [SFinite μ']
    (F : X → ℂ) (δ : X → ℝ) (F' : X' → ℂ) (δ' : X' → ℝ)
    (hF : AEStronglyMeasurable F μ) (hF' : AEStronglyMeasurable F' μ')
    (hδm : Measurable δ) (hδ'm : Measurable δ') (hδ : ∀ x, 0 < δ x) (hδ' : ∀ x, 0 < δ' x)
    (h k : ℝ → ℂ) (hh : Measurable h) (hk : Measurable k) (hhd : RapidDecay h)
    (hkd : RapidDecay k) (N : ℝ)
    (hFN : ∀ σ : ℝ, N ≤ σ → Integrable (fun x => ‖F x‖ * δ x ^ σ) μ)
    (hF'N : ∀ σ : ℝ, N ≤ σ → Integrable (fun x => ‖F' x‖ * δ' x ^ σ) μ')
    (hpair : ∀ a : ℝ, 0 < a → theta μ F δ h a = (a : ℂ) * theta μ' F' δ' k a⁻¹) :
    Differentiable ℂ (fun s : ℂ => mellin (theta μ F δ h) (-s)) ∧
    (∀ s : ℂ, N ≤ s.re →
      mellin (theta μ F δ h) (-s) = (∫ x, F x * (δ x : ℂ) ^ s ∂μ) * mellin h (-s)) ∧
    (∀ s : ℂ, s.re ≤ 1 - N →
      mellin (theta μ F δ h) (-s) =
        (∫ x, F' x * (δ' x : ℂ) ^ (1 - s) ∂μ') * mellin k (s - 1)) := by
  have hdec := theta_rapidDecay μ μ' F δ F' δ' hδ hδ' hhd hkd hFN hF'N hpair
  have hm : AEStronglyMeasurable (theta μ F δ h) volume :=
    aestronglyMeasurable_theta μ F δ hF hδm h hh volume
  refine ⟨(hdec.differentiable_mellin hm).comp differentiable_neg, fun s hs => ?_,
    fun s hs => ?_⟩
  · exact mellin_theta μ F δ hF hδm hδ h hh hhd s (hFN s.re hs)
  · have h1 : mellin (theta μ F δ h) (-s) =
        mellin (fun a : ℝ => (a : ℂ) ^ (1 : ℂ) • theta μ' F' δ' k a⁻¹) (-s) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun a ha => ?_
      simp only [Complex.cpow_one, smul_eq_mul]
      rw [hpair a ha]
    have h2 := mellin_theta μ' F' δ' hF' hδ'm hδ' k hk hkd (1 - s)
      (hF'N _ (by simp only [Complex.sub_re, Complex.one_re]; linarith))
    rw [h1, mellin_cpow_smul, mellin_comp_inv, show -(-s + 1) = -(1 - s) by ring, h2,
      neg_sub]

/-- Continuation and functional equation from a pair identity (Jacquet 2009, Proposition 4.1,
in the shape of the continuation part of an equation package). -/
theorem exists_continuation {X X' : Type*} [MeasurableSpace X] [MeasurableSpace X']
    (μ : Measure X) (μ' : Measure X') [SFinite μ] [SFinite μ']
    (F : X → ℂ) (δ : X → ℝ) (F' : X' → ℂ) (δ' : X' → ℝ)
    (hF : AEStronglyMeasurable F μ) (hF' : AEStronglyMeasurable F' μ')
    (hδm : Measurable δ) (hδ'm : Measurable δ') (hδ : ∀ x, 0 < δ x) (hδ' : ∀ x, 0 < δ' x)
    (h k : ℝ → ℂ) (hh : Measurable h) (hk : Measurable k) (hhd : RapidDecay h)
    (hkd : RapidDecay k) (N : ℝ)
    (hFN : ∀ σ : ℝ, N ≤ σ → Integrable (fun x => ‖F x‖ * δ x ^ σ) μ)
    (hF'N : ∀ σ : ℝ, N ≤ σ → Integrable (fun x => ‖F' x‖ * δ' x ^ σ) μ')
    (hpair : ∀ a : ℝ, 0 < a → theta μ F δ h a = (a : ℂ) * theta μ' F' δ' k a⁻¹)
    (σ₁ : ℝ) (hh0 : ∀ s : ℂ, σ₁ < s.re → mellin h (-s) ≠ 0)
    (hk0 : ∀ s : ℂ, σ₁ < s.re → mellin k (-s) ≠ 0)
    (Z Zd L Ld E : ℂ → ℂ) (sign : ℂ)
    (hZ : ∀ s : ℂ, N ≤ s.re → Z s = ∫ x, F x * (δ x : ℂ) ^ s ∂μ)
    (hZd : ∀ s : ℂ, N ≤ s.re → Zd s = ∫ x, F' x * (δ' x : ℂ) ^ s ∂μ')
    (hfac : ∀ᶠ s in codiscrete ℂ,
      L s * mellin h (-s) = sign * E s * Ld (1 - s) * mellin k (s - 1)) :
    ∃ (σ : ℝ) (M Md : ℂ → ℂ),
      MeromorphicOn M univ ∧ MeromorphicOn Md univ ∧
      (∀ s : ℂ, σ < s.re → Z s = M s) ∧
      (∀ s : ℂ, σ < s.re → Zd s = Md s) ∧
      ∀ᶠ s in codiscrete ℂ, L s * Md (1 - s) = sign * E s * Ld (1 - s) * M s := by
  obtain ⟨hΘ, hΘ1, hΘ2⟩ := mellin_theta_entire μ μ' F δ F' δ' hF hF' hδm hδ'm hδ hδ' h k hh hk
    hhd hkd N hFN hF'N hpair
  set Θ : ℂ → ℂ := fun s => mellin (theta μ F δ h) (-s) with hΘdef
  have hmh : Differentiable ℂ (fun s : ℂ => mellin h (-s)) :=
    (hhd.differentiable_mellin hh.aestronglyMeasurable).comp differentiable_neg
  have hmk : Differentiable ℂ (fun s : ℂ => mellin k (s - 1)) :=
    (hkd.differentiable_mellin hk.aestronglyMeasurable).comp (differentiable_id.sub_const 1)
  have hmk' : Differentiable ℂ (fun s : ℂ => mellin k (-s)) :=
    (hkd.differentiable_mellin hk.aestronglyMeasurable).comp differentiable_neg
  have hΘ' : Differentiable ℂ (fun s : ℂ => Θ (1 - s)) := hΘ.comp (differentiable_id.const_sub 1)
  refine ⟨max N σ₁, fun s => Θ s / mellin h (-s), fun s => Θ (1 - s) / mellin k (-s),
    fun z _ => ?_, fun z _ => ?_, fun s hs => ?_, fun s hs => ?_, ?_⟩
  · exact ((hΘ.analyticAt z).meromorphicAt).div ((hmh.analyticAt z).meromorphicAt)
  · exact ((hΘ'.analyticAt z).meromorphicAt).div ((hmk'.analyticAt z).meromorphicAt)
  · have hN : N ≤ s.re := (le_max_left _ _).trans hs.le
    have hσ : σ₁ < s.re := lt_of_le_of_lt (le_max_right _ _) hs
    simp only [hΘdef]
    rw [hΘ1 s hN, mul_div_cancel_right₀ _ (hh0 s hσ), hZ s hN]
  · have hN : N ≤ s.re := (le_max_left _ _).trans hs.le
    have hσ : σ₁ < s.re := lt_of_le_of_lt (le_max_right _ _) hs
    have hre : (1 - s).re ≤ 1 - N := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    simp only [hΘdef]
    rw [hΘ2 (1 - s) hre, sub_sub_cancel, show (1 - s) - 1 = -s by ring,
      mul_div_cancel_right₀ _ (hk0 s hσ), hZd s hN]
  · have hA : AnalyticOnNhd ℂ (fun s : ℂ => mellin h (-s)) univ :=
      fun z _ => hmh.analyticAt z
    have hB : AnalyticOnNhd ℂ (fun s : ℂ => mellin k (s - 1)) univ :=
      fun z _ => hmk.analyticAt z
    have hA0 := hA.preimage_zero_mem_codiscrete (x := ((σ₁ + 1 : ℝ) : ℂ))
      (hh0 _ (by simp))
    have hB0 := hB.preimage_zero_mem_codiscrete (x := ((-σ₁ : ℝ) : ℂ)) (by
      have := hk0 ((1 + σ₁ : ℝ) : ℂ) (by simp)
      convert this using 2
      push_cast
      ring)
    filter_upwards [hfac, hA0, hB0] with s hs h1 h2
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at h1 h2
    simp only [hΘdef, sub_sub_cancel, show -(1 - s) = s - 1 by ring]
    rw [mul_div_assoc', mul_div_assoc', div_eq_div_iff h2 h1]
    linear_combination (mellin (theta μ F δ h) (-s)) * hs

end Langlands.Global.RankinSelbergGlobal.ArchimedeanMellinPair

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanMellinPair

/-- Continuation and functional equation from a Mellin pair identity: the core of Jacquet 2009,
Proposition 4.1, for a positive function `δ` on a measure space in place of `|x|` on `F^×`, with
the conclusion in the shape of the continuation part of an equation package. -/
def MellinPairContinuationStatement : Prop :=
  ∀ {X : Type u} {X' : Type v} [MeasurableSpace X] [MeasurableSpace X']
    (μ : Measure X) (μ' : Measure X') [SFinite μ] [SFinite μ']
    (F : X → ℂ) (δ : X → ℝ) (F' : X' → ℂ) (δ' : X' → ℝ)
    (h k : ℝ → ℂ) (N σ₁ : ℝ) (Z Zd L Ld E : ℂ → ℂ) (sign : ℂ),
    AEStronglyMeasurable F μ → AEStronglyMeasurable F' μ' →
    Measurable δ → Measurable δ' → (∀ x, 0 < δ x) → (∀ x, 0 < δ' x) →
    Measurable h → Measurable k → RapidDecay h → RapidDecay k →
    (∀ σ : ℝ, N ≤ σ → Integrable (fun x => ‖F x‖ * δ x ^ σ) μ) →
    (∀ σ : ℝ, N ≤ σ → Integrable (fun x => ‖F' x‖ * δ' x ^ σ) μ') →
    (∀ a : ℝ, 0 < a → theta μ F δ h a = (a : ℂ) * theta μ' F' δ' k a⁻¹) →
    (∀ s : ℂ, σ₁ < s.re → mellin h (-s) ≠ 0) →
    (∀ s : ℂ, σ₁ < s.re → mellin k (-s) ≠ 0) →
    (∀ s : ℂ, N ≤ s.re → Z s = ∫ x, F x * (δ x : ℂ) ^ s ∂μ) →
    (∀ s : ℂ, N ≤ s.re → Zd s = ∫ x, F' x * (δ' x : ℂ) ^ s ∂μ') →
    (∀ᶠ s in codiscrete ℂ,
      L s * mellin h (-s) = sign * E s * Ld (1 - s) * mellin k (s - 1)) →
    ∃ (σ : ℝ) (M Md : ℂ → ℂ),
      MeromorphicOn M univ ∧ MeromorphicOn Md univ ∧
      (∀ s : ℂ, σ < s.re → Z s = M s) ∧
      (∀ s : ℂ, σ < s.re → Zd s = Md s) ∧
      ∀ᶠ s in codiscrete ℂ, L s * Md (1 - s) = sign * E s * Ld (1 - s) * M s

theorem mellinPairContinuation : MellinPairContinuationStatement.{u, v} := by
  intro X X' _ _ μ μ' _ _ F δ F' δ' h k N σ₁ Z Zd L Ld E sign hF hF' hδm hδ'm hδ hδ' hh hk
    hhd hkd hFN hF'N hpair hh0 hk0 hZ hZd hfac
  exact exists_continuation μ μ' F δ F' δ' hF hF' hδm hδ'm hδ hδ' h k hh hk hhd hkd N hFN hF'N
    hpair σ₁ hh0 hk0 Z Zd L Ld E sign hZ hZd hfac

end Langlands.Global.RankinSelbergGlobal
