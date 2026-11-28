import Langlands.Global.RankinSelberg.RealOrdinaryRowLocalization
import Langlands.Global.RankinSelberg.RealUnequalLastRowDescent
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Descent from real equal-rank ordinary integrals to adjacent ranks -/

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff ENNReal NNReal Matrix.Norms.Operator SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealEqualOrdinaryDescent

open Langlands.GeneralLinear Langlands.QuotientIntegration
open Langlands.RankinSelberg (LeftUnipotentQuotient det_rankInclusion)
open ArchimedeanLocal RealEqualConvergence RealConvergenceAnalysis RealOrdinaryRowLocalization
open RealLowerBlockChart (quotientDensity rowEquiv unitsLower det_ne_zero)
open RealUnequalFamily (HasLeftCharacter HasUniformGauge ordinary_halfPlaneDomination continuous_integrand)
open RealUnequalLastRowDescent (hasLeftCharacter_translate hasLeftCharacter_pad
  hasUniformGauge_translate hasUniformGauge_pad_translate eq_zero_on_right)
open RealWhittakerTranslatedMellin (HasGaugeBound)
open RealUnequalMellinReduction (quotientDetAbs quotientDetAbs_pos continuous_quotientDetAbs)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable archimedeanRealQBorel
  RealRankZero.unitsMeasurable RealRankZero.unitsBorel

local notation "G" => fun n => Langlands.GeneralLinear (n + 1) ℝ
local notation "N" => fun n => Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ
local notation "Q" => fun n => LeftUnipotentQuotient n ℝ
local notation "Row" => fun n => Fin (n + 1) → ℝ
local notation "Z" => fun n => Row n × ℝˣ

variable {n : ℕ}

private theorem product_invariant {a : ℝˣ} {W V : G n → ℂ}
    (hW : HasLeftCharacter a W) (hV : HasLeftCharacter (-a) V) :
    ∀ u ∈ N n, ∀ g, W (u * g) * V (u * g) = W g * V g := by
  intro u hu g
  rw [hW u hu, hV u hu, mul_mul_mul_comm, realWhittakerCharacter_mul_neg, one_mul]

private theorem gauge_of_bound {W : G n → ℂ} (h : HasGaugeBound W) : HasGauge W := by
  obtain ⟨A, hA⟩ := h
  refine ⟨A, fun M => ?_⟩
  obtain ⟨C, hC, hle⟩ := hA M
  refine ⟨C, hC, fun y k => ?_⟩
  simpa only [RealIwasawa.alpha_torus_mul_unitary] using hle (RealIwasawa.torus y * k.val)

private theorem smooth_rowCharacter {m : ℕ} (b : Fin m → ℝ) : ContDiff ℝ ∞ (rowCharacter b) := by
  change ContDiff ℝ ∞ (fun η : Fin m → ℝ =>
    Complex.exp ((↑(2 * Real.pi * ∑ i, η i * b i) : ℂ) * Complex.I))
  have h : ContDiff ℝ ∞ (fun η : Fin m → ℝ => 2 * Real.pi * ∑ i, η i * b i) := by fun_prop
  exact (((Complex.ofRealCLM.contDiff.comp h).mul contDiff_const).cexp)

private theorem exists_row_test (η : Row n) :
    ∃ (Φ : 𝓢(Row n, ℂ)), Φ η = 1 ∧ HasCompactSupport (Φ : Row n → ℂ) := by
  obtain ⟨f, -, hf, hfd, -, h1⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    (s := univ) (x := η) univ_mem
  let hc : HasCompactSupport (Complex.ofRealCLM ∘ f) := hf.comp_left rfl
  exact ⟨hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hfd), by simpa using h1, hc⟩

private theorem holomorphic_modulation (D : RealQuotientMeasureData n)
    {a : ℝˣ} {W V : G n → ℂ} (hW : HasLeftCharacter a W) (hV : HasLeftCharacter (-a) V)
    (hWc : Continuous W) (hVc : Continuous V) {Φ Ψ : Row n → ℂ} (hΨ : Continuous Ψ)
    (habs : ∀ η, ‖Ψ η‖ = ‖Φ η‖) {σ : ℝ}
    (hi : ∀ s : ℂ, σ < s.re → Integrable (realEqualIntegrand W V Φ s) D.measure) :
    DifferentiableOn ℂ (realEqualIntegral D W V Ψ) {s : ℂ | σ < s.re} := by
  let f (q : Q n) := kernel W V Ψ q.out
  let ℓ (q : Q n) := logDet q.out
  have hkinv := fun u : N n => kernel_unipotent_mul (Φ := Ψ) (product_invariant hW hV) u
  have hlinv := fun u : N n => logDet_unipotent_mul u
  have hfm : AEStronglyMeasurable f D.measure := by
    simp only [f, out_eq_descend _ hkinv]
    exact (continuous_descend hkinv (continuous_kernel hWc hVc hΨ)).aestronglyMeasurable
  have hℓm : AEStronglyMeasurable ℓ D.measure := by
    simp only [ℓ, out_eq_descend _ hlinv]
    exact (continuous_descend_real hlinv continuous_logDet).aestronglyMeasurable
  change DifferentiableOn ℂ (fun s : ℂ => ∫ q, f q * Complex.exp (s * (ℓ q : ℂ)) ∂D.measure)
    {s : ℂ | σ < s.re}
  refine differentiableOn_integral_cexp_mul hfm hℓm fun t ht => ?_
  exact ((hi (t : ℂ) (by simpa using ht)).norm).congr (ae_of_all _ fun q => by
    simp only [realEqualIntegrand_eq, kernel, f, ℓ, norm_mul, norm_cexp_mul_ofReal, Complex.ofReal_re, habs])

private def lowerIntegral (D : RealQuotientMeasureData n) (W V : G (n + 1) → ℂ)
    (s : ℂ) (L : G (n + 1)) : ℂ :=
  realUnequalIntegral (Nat.lt_succ_self n) D (fun g => W (g * L))
    (fun g => V (padGL (Nat.le_succ (n + 1)) g * L)) s

set_option maxHeartbeats 800000 in
private theorem continuousAt_lowerIntegral (D : RealQuotientMeasureData n)
    {a : ℝˣ} {W V : G (n + 1) → ℂ} (hW : HasLeftCharacter a W) (hV : HasLeftCharacter (-a) V)
    (hWc : Continuous W) (hVc : Continuous V) (hWg : HasGaugeBound W) (hVg : HasGaugeBound V) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ContinuousAt (lowerIntegral D W V s) 1 := by
  obtain ⟨K, hKc, hK⟩ := exists_compact_mem_nhds (1 : G (n + 1))
  let S : Set (G (n + 1) × ℂ) := K ×ˢ univ
  let Wf (p : G (n + 1) × ℂ) (g : G (n + 1)) := W (g * p.1)
  let Vf (p : G (n + 1) × ℂ) (g : G n) := V (padGL (Nat.le_succ (n + 1)) g * p.1)
  have hWl (p) : HasLeftCharacter a (Wf p) := hasLeftCharacter_translate hW p.1
  have hVl (p) : HasLeftCharacter (-a) (Vf p) :=
    hasLeftCharacter_pad (hasLeftCharacter_translate hV p.1) _
  have hWb : HasUniformGauge S Wf := hasUniformGauge_translate hWg hKc S Prod.fst (fun _ hp => hp.1)
  have hVb : HasUniformGauge S Vf := hasUniformGauge_pad_translate hVg hKc S Prod.fst (fun _ hp => hp.1)
  obtain ⟨σ, hdom⟩ := ordinary_halfPlaneDomination (Nat.lt_succ_self n) D S Wf Vf Prod.snd hWl hVl hWb hVb
  refine ⟨σ, fun s hs => ?_⟩
  obtain ⟨B, hBi, hB⟩ := hdom s.re
  change ContinuousAt (fun L => ∫ q, realUnequalIntegrand (Nat.lt_succ_self n) (Wf (L, s)) (Vf (L, s)) s q
    ∂D.measure) 1
  refine continuousAt_of_dominated ?_ ?_ hBi ?_
  · exact Eventually.of_forall fun L => (continuous_integrand (Nat.lt_succ_self n) (hWl (L, s)) (hVl (L, s))
      (hWc.comp (continuous_id.mul continuous_const))
      (hVc.comp ((UnequalAnalytic.continuous_padGL _).mul continuous_const)) s).aestronglyMeasurable
  · filter_upwards [hK] with L hL
    exact ae_of_all _ fun q => hB (L, s) ⟨hL, mem_univ _⟩ hs le_rfl q
  · refine ae_of_all _ fun q => ?_
    change ContinuousAt (fun L : G (n + 1) => W (padGL _ q.out * L) * V (padGL _ q.out * L) *
      ArchimedeanLocal.detPower realNormalizedAbs q.out (s - ((n + 1 - n : ℕ) : ℂ) / 2)) 1
    exact (((hWc.comp (continuous_const.mul continuous_id)).mul
      (hVc.comp (continuous_const.mul continuous_id))).mul continuous_const).continuousAt

private theorem rankInclusion_eq_pad (g : G n) : rankInclusion 1 g = padGL (Nat.le_succ (n + 1)) g := by
  rw [← Langlands.RankinSelberg.InducedTailIntermediate.lowerBlockPair_zero_one,
    RealUnequalLastRowDescent.lowerBlockPair_zero_one]

private theorem logDet_rankInclusion_mul (g : G n) (L : G (n + 1)) :
    logDet (rankInclusion 1 g * L) = logDet g + logDet L := by
  simp only [logDet, realNormalizedAbs, Units.val_mul, Matrix.det_mul, det_rankInclusion, abs_mul]
  exact Real.log_mul (abs_ne_zero.mpr (det_ne_zero g)) (abs_ne_zero.mpr (det_ne_zero L))

private theorem fiber_equalKernel (D : RealQuotientMeasureData n) (W V : G (n + 1) → ℂ)
    (Φ : Row (n + 1) → ℂ) (s : ℂ) (z : Z n) :
    fiber D (fun g => kernel W V Φ g * Complex.exp (s * (logDet g : ℂ))) z =
      (Φ (row z) * Complex.exp (s * (logDet (sectionGL z) : ℂ))) *
        lowerIntegral D W V (s - 1 / 2) (sectionGL z) := by
  have hd : Measurable (fun q : Q n => ((quotientDetAbs q)⁻¹).toNNReal) :=
    (continuous_real_toNNReal.comp (continuous_quotientDetAbs.inv₀
      fun q => (quotientDetAbs_pos q).ne')).measurable
  change (∫ q, _ ∂D.measure.withDensity (quotientDensity n)) = _
  rw [show quotientDensity n = fun q => (((quotientDetAbs q)⁻¹).toNNReal : ℝ≥0∞) from rfl,
    integral_withDensity_eq_integral_smul hd]
  change _ = _ * ∫ q, realUnequalIntegrand (Nat.lt_succ_self n) (fun g => W (g * sectionGL z))
    (fun g => V (padGL (Nat.le_succ (n + 1)) g * sectionGL z)) (s - 1 / 2) q ∂D.measure
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  have hrow : Langlands.RankinSelberg.lastRow (rankInclusion 1 q.out * sectionGL z) = row z := by
    rw [sectionGL, rankInclusion_mul_lowerBlockPair, mul_one, lastRow_lowerBlock]
  have hδ : (quotientDetAbs q)⁻¹ = Real.exp (-logDet q.out) := by
    rw [Real.exp_neg]
    change (quotientDetAbs q)⁻¹ = (Real.exp (Real.log (quotientDetAbs q)))⁻¹
    rw [Real.exp_log (quotientDetAbs_pos q)]
  have harg : s - 1 / 2 - ((n + 1 - n : ℕ) : ℂ) / 2 = s - 1 := by
    rw [Nat.add_sub_cancel_left]
    ring
  change ((quotientDetAbs q)⁻¹).toNNReal •
      (kernel W V Φ (rankInclusion 1 q.out * sectionGL z) *
        Complex.exp (s * (logDet (rankInclusion 1 q.out * sectionGL z) : ℂ))) =
    _ * (W (padGL (Nat.le_succ (n + 1)) q.out * sectionGL z) *
      V (padGL (Nat.le_succ (n + 1)) q.out * sectionGL z) *
      Complex.exp ((s - 1 / 2 - ((n + 1 - n : ℕ) : ℂ) / 2) * (logDet q.out : ℂ)))
  rw [NNReal.smul_def, Complex.real_smul, Real.coe_toNNReal _ (inv_nonneg.mpr (quotientDetAbs_pos q).le),
    kernel, hrow, logDet_rankInclusion_mul, rankInclusion_eq_pad, harg,
    hδ, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_add]
  rw [mul_add, Complex.exp_add, sub_mul, one_mul, sub_eq_add_neg, Complex.exp_add]
  ring

/-- If the ordinary equal-rank integral vanishes on a right half-plane for each Schwartz
row test, the adjacent-rank ordinary integral with the second coefficient restricted to
the standard leading block also vanishes on a right half-plane. -/
def RealEqualOrdinaryDescentStatement : Prop :=
  ∀ (n : ℕ) (D : RealQuotientMeasureData n) (E : RealQuotientMeasureData (n + 1))
    (a : ℝˣ) (W V : G (n + 1) → ℂ), HasLeftCharacter a W → HasLeftCharacter (-a) V →
    Continuous W → Continuous V → HasGaugeBound W → HasGaugeBound V →
    (∀ Φ : 𝓢(Row (n + 1), ℂ), ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → realEqualIntegral E W V Φ s = 0) →
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → realUnequalIntegral (Nat.lt_succ_self n) D W
      (fun g => V (padGL (Nat.le_succ (n + 1)) g)) s = 0

set_option maxHeartbeats 1200000 in
theorem realEqualOrdinaryDescent : RealEqualOrdinaryDescentStatement := by
  intro n D E a W V hW hV hWc hVc hWg hVg hvan
  obtain ⟨Φ, hΦ, hΦsupp⟩ := exists_row_test (row (r := n) (0, 1))
  obtain ⟨σ₀, hint, -⟩ := exists_convergence E hWc hVc Φ.continuous (product_invariant hW hV)
    (gauge_of_bound hWg) (gauge_of_bound hVg) (hasRapidDecay_schwartz Φ)
  obtain ⟨σ₁, hlow⟩ := continuousAt_lowerIntegral D hW hV hWc hVc hWg hVg
  refine ⟨max σ₀ σ₁, fun s hs => ?_⟩
  let t : ℂ := s + 1 / 2
  have ht : σ₀ < t.re := by
    have := (le_max_left _ _).trans_lt hs
    simp only [t, Complex.add_re]
    norm_num
    linarith
  have hts : t - 1 / 2 = s := by dsimp [t]; ring
  let F : G (n + 1) → ℂ := fun g => kernel W V Φ g * Complex.exp (t * (logDet g : ℂ))
  have hFc : Continuous F := (continuous_kernel hWc hVc Φ.continuous).mul
    (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp continuous_logDet)))
  have hFinv (u : N (n + 1)) (g : G (n + 1)) : F (u.val * g) = F g := by
    simp only [F, kernel_unipotent_mul (product_invariant hW hV), logDet_unipotent_mul]
  have hfe : fiber D F = fun z =>
      (Φ (row z) * Complex.exp (t * (logDet (sectionGL z) : ℂ))) *
        lowerIntegral D W V s (sectionGL z) := by
    funext z
    exact (fiber_equalKernel D W V Φ t z).trans (by rw [hts])
  have hFfiber : ContinuousAt (fiber D F) (0, 1) := by
    rw [hfe]
    have hrow : Continuous (row (r := n)) := by
      apply continuous_pi
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [row, Fin.snoc_last, Function.comp_def] using
          (Units.continuous_val.comp continuous_snd : Continuous (Units.val ∘ Prod.snd : Z n → ℝ))
      · simpa only [row, Fin.snoc_castSucc, Function.comp_def] using
          ((continuous_apply j).comp continuous_fst : Continuous ((fun x : Row n => x j) ∘ Prod.fst : Z n → ℝ))
    have hsec : ContinuousAt (sectionGL (r := n)) (0, 1) := continuous_sectionGL.continuousAt
    have hlow' := hlow s ((le_max_right _ _).trans_lt hs)
    have hlow'' : ContinuousAt (lowerIntegral D W V s) (sectionGL (r := n) (0, 1)) := by
      simpa only [sectionGL_standard] using hlow'
    have hexp : Continuous (fun z : Z n => Complex.exp (t * (logDet (sectionGL z) : ℂ))) :=
      Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_logDet.comp continuous_sectionGL)))
    exact ((Φ.continuous.comp hrow).continuousAt.mul hexp.continuousAt).mul (hlow''.comp hsec)
  have hzero := realOrdinaryRowLocalization n D E F hFc hFinv (hint t ht) hFfiber (fun b => ?_)
  · simp only [hfe, hΦ, sectionGL_standard, logDet, Units.val_one,
      Matrix.det_one, realNormalizedAbs, abs_one, Real.log_one, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, mul_one, one_mul] at hzero
    simpa only [lowerIntegral, mul_one] using hzero
  · let Ψ : 𝓢(Row (n + 1), ℂ) := (hΦsupp.mul_left (f := rowCharacter b)).toSchwartzMap
      ((smooth_rowCharacter b).mul Φ.smooth')
    have hΨ (η) : Ψ η = rowCharacter b η * Φ η := rfl
    have hhol := holomorphic_modulation E hW hV hWc hVc Ψ.continuous
      (fun η => by rw [hΨ, norm_mul, norm_rowCharacter, one_mul]) hint
    obtain ⟨τ, hτ⟩ := hvan Ψ
    rw [← eq_zero_on_right hhol hτ t ht]
    change _ = ∫ q, realEqualIntegrand W V Ψ t q ∂E.measure
    refine integral_congr_ae (ae_of_all _ fun q => ?_)
    simp only [realEqualIntegrand_eq, F, kernel, hΨ]
    ring

end Langlands.Global.RankinSelbergGlobal.RealEqualOrdinaryDescent
