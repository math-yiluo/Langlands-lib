import Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationReduction
import Langlands.Global.RankinSelberg.UnequalAnalyticHolomorphy
import Mathlib.MeasureTheory.Integral.Prod

/-! # Analytic reduction for the local complex unequal-rank equation -/

noncomputable section

open MeasureTheory Metric
open Langlands.LocalFactor (ReciprocalEntire)
open Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal

private theorem differentiableOn_integral_of_exp_shift
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {K : ℂ → X → ℂ} {L : X → ℝ}
    {σ : ℝ} (hL : AEStronglyMeasurable L μ)
    (hshift : ∀ s z x, K s x = K z x * Complex.exp ((s - z) * (L x : ℂ)))
    (hint : ∀ s : ℂ, σ < s.re → Integrable (K s) μ) :
    DifferentiableOn ℂ (fun s => ∫ x, K s x ∂μ) {s : ℂ | σ < s.re} := by
  intro z hz
  change σ < z.re at hz
  let δ : ℝ := (z.re - σ) / 3
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let b : ℝ := 2 * δ
  have hplus : σ < (z + (b : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    dsimp [b, δ]
    linarith
  have hminus : σ < (z - (b : ℂ)).re := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    dsimp [b, δ]
    linarith
  have hK : Integrable (K z) μ := hint z hz
  let K' : ℂ → X → ℂ := fun s x => K s x * (L x : ℂ)
  let bound : X → ℝ := fun x =>
    (‖K (z + (b : ℂ)) x‖ + 2 * ‖K z x‖ + ‖K (z - (b : ℂ)) x‖) / δ
  have hbound : Integrable bound μ := by
    have h := (((hint _ hplus).norm.add (hK.norm.const_mul 2)).add
      (hint _ hminus).norm).const_mul δ⁻¹
    exact h.congr (Filter.Eventually.of_forall fun x => by simp [bound, div_eq_mul_inv, mul_comm])
  have hnorm : ∀ s x, ‖K s x‖ = ‖K z x‖ * Real.exp ((s - z).re * L x) := by
    intro s x
    rw [hshift s z x, UnequalAnalytic.norm_mul_cexp]
  have hle : ∀ x, ∀ s ∈ ball z δ, ‖K' s x‖ ≤ bound x := by
    intro x s hs
    have hre : |(s - z).re| ≤ δ :=
      (Complex.abs_re_le_norm _).trans (mem_ball_iff_norm.mp hs).le
    have h := UnequalAnalytic.abs_mul_exp_le (a := 0) (σ := (s - z).re / δ) (δ * L x)
      (by simpa [abs_div, abs_of_pos hδ] using (div_le_one hδ).mpr hre)
    have hexp : (s - z).re / δ * (δ * L x) = (s - z).re * L x := by
      rw [← mul_assoc, div_mul_cancel₀ _ hδ.ne']
    rw [hexp] at h
    have h₁ : (z + (b : ℂ) - z).re = b := by simp
    have h₂ : (z - (b : ℂ) - z).re = -b := by
      simp only [Complex.sub_re, Complex.ofReal_re]
      ring
    apply (le_div_iff₀ hδ).mpr
    simp only [K', norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm s x, hnorm (z + (b : ℂ)) x, hnorm (z - (b : ℂ)) x, h₁, h₂]
    calc
      ‖K z x‖ * Real.exp ((s - z).re * L x) * |L x| * δ =
          ‖K z x‖ * (|δ * L x| * Real.exp ((s - z).re * L x)) := by
        rw [abs_mul, abs_of_pos hδ]
        ring
      _ ≤ ‖K z x‖ * (Real.exp (b * L x) + 2 + Real.exp (-b * L x)) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        simpa [b, mul_assoc, neg_mul] using h
      _ = _ := by ring
  have hderiv : ∀ x s, HasDerivAt (fun s => K s x) (K' s x) s := by
    intro x s
    have h := ((hasDerivAt_id s).sub_const z).mul_const (L x : ℂ)
    simp only [id, one_mul] at h
    have heq : (fun w => K w x) = fun w => K z x * Complex.exp ((w - z) * (L x : ℂ)) :=
      funext fun w => hshift w z x
    rw [heq]
    simpa only [K', hshift s z x, mul_assoc] using h.cexp.const_mul (K z x)
  have hmeas : ∀ᶠ s in nhds z, AEStronglyMeasurable (K s) μ := by
    have hopen : {s : ℂ | σ < s.re} ∈ nhds z :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
    filter_upwards [hopen] with s hs
    exact (hint s hs).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (K' z) μ :=
    hK.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable hL)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds z hδ) hmeas hK
    hmeas' (Filter.Eventually.of_forall hle) hbound
    (Filter.Eventually.of_forall fun x s _ => hderiv x s)).2.differentiableAt.differentiableWithinAt

attribute [local instance] archimedeanComplexGLMeasurable archimedeanComplexGLBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel archimedeanComplexQMeasurable
  archimedeanComplexQBorel

private theorem measurable_detLog (t : ℕ) :
    Measurable (fun q : LeftUnipotentQuotient t ℂ =>
      Real.log (complexNormalizedAbs (Matrix.det q.out.val))) := by
  let Δ : LeftUnipotentQuotient t ℂ → ℂ :=
    QuotientIntegration.descend (GeneralLinear.upperUnipotent (t + 1) ℂ)
      (fun g => Matrix.det g.val) fun u g => by
        change Matrix.det (u.val.val * g.val) = _
        rw [Matrix.det_mul, RankinSelberg.unipotent_det, one_mul]
  have hΔ : Continuous Δ := by
    unfold Δ QuotientIntegration.descend
    exact Units.continuous_val.matrix_det.quotient_lift _
  have heq (q : LeftUnipotentQuotient t ℂ) : Δ q = Matrix.det q.out.val := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  simp only [← heq]
  exact Real.measurable_log.comp (hΔ.norm.pow 2).measurable

private theorem detPower_shift {n : ℕ} (g : Langlands.GeneralLinear n ℂ) (s z k : ℂ) :
    ArchimedeanLocal.detPower complexNormalizedAbs g (s - k) =
      ArchimedeanLocal.detPower complexNormalizedAbs g (z - k) *
        Complex.exp ((s - z) * (Real.log (complexNormalizedAbs (Matrix.det g.val)) : ℂ)) := by
  simp only [ArchimedeanLocal.detPower, ← Complex.exp_add]
  congr 1
  ring

section IntegralHolomorphy

variable {r t : ℕ} (h : t < r) (a : ℂˣ) (D : ComplexQuotientMeasureData t)
  (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℂ → ℂ)

private theorem complexUnequalDualIntegral_eq_prod (s : ℂ)
    (hint : Integrable (complexUnequalDualKernel h W W' s) (complexUnequalDualMeasure (r := r) a D)) :
    complexUnequalDualIntegral h a D W W' s =
      ∫ p, complexUnequalDualKernel h W W' s p ∂complexUnequalDualMeasure (r := r) a D := by
  have : SecondCountableTopology (Matrix (Fin (t + 1)) (Fin (t + 1)) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin (t + 1) → Fin (t + 1) → ℂ))
  have : SecondCountableTopology (Matrix (Fin (t + 1)) (Fin (t + 1)) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  have : SecondCountableTopology (Langlands.GeneralLinear (t + 1) ℂ) :=
    Units.isInducing_embedProduct.secondCountableTopology
  have : LocallyCompactSpace (Matrix (Fin (t + 1)) (Fin (t + 1)) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin (t + 1) → Fin (t + 1) → ℂ))
  have : SigmaCompactSpace (LeftUnipotentQuotient t ℂ) := by
    have hq := QuotientIntegration.leftQuotient_isOpenQuotientMap
      (GeneralLinear.upperUnipotent (t + 1) ℂ)
    apply isSigmaCompact_univ_iff.mp
    rw [← Set.range_eq_univ.mpr hq.surjective]
    exact isSigmaCompact_range hq.continuous
  have : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  have : D.measure.Regular := D.compatible.regular
  exact (integral_prod _ hint).symm

private theorem differentiableOn_complexUnequalIntegral {σ : ℝ}
    (hint : ∀ s : ℂ, σ < s.re → Integrable (complexUnequalIntegrand h W W' s) D.measure) :
    DifferentiableOn ℂ (complexUnequalIntegral h D W W') {s : ℂ | σ < s.re} := by
  refine differentiableOn_integral_of_exp_shift (K := complexUnequalIntegrand h W W')
    (measurable_detLog t).aestronglyMeasurable ?_ hint
  intro s z q
  simp only [complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand,
    detPower_shift q.out s z, mul_assoc]

private theorem differentiableOn_complexUnequalDualIntegral {σ : ℝ}
    (hint : ∀ s : ℂ, σ < s.re → Integrable (complexUnequalDualKernel h W W' s)
      (complexUnequalDualMeasure (r := r) a D)) :
    DifferentiableOn ℂ (complexUnequalDualIntegral h a D W W') {s : ℂ | σ < s.re} := by
  refine (differentiableOn_integral_of_exp_shift (K := complexUnequalDualKernel h W W')
    ((measurable_detLog t).comp measurable_fst).aestronglyMeasurable ?_ hint).congr
    (fun s hs => complexUnequalDualIntegral_eq_prod h a D W W' s (hint s hs))
  intro s z p
  simp only [complexUnequalDualKernel, blockKernel, detPower_shift p.1.out s z, mul_assoc,
    Function.comp_apply]

end IntegralHolomorphy

/-! ### Extension from intertwiner values -/

private def normalizedKernelPairs {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (L Ld E : ℂ → ℂ) :
    Submodule ℂ ((ℂ → X → ℂ) × (ℂ → Y → ℂ)) where
  carrier := {K | ∃ (σ : ℝ) (N Nd : ℂ → ℂ),
    Differentiable ℂ N ∧ Differentiable ℂ Nd ∧
    (∀ s : ℂ, σ < s.re →
      Integrable (K.1 s) μ ∧ Integrable (K.2 s) ν ∧
      N s = L s * (∫ x, K.1 s x ∂μ) ∧ Nd s = Ld s * (∫ y, K.2 s y ∂ν)) ∧
    ∀ s : ℂ, Nd (1 - s) = E s * N s}
  zero_mem' := by
    refine ⟨0, 0, 0, differentiable_const 0, differentiable_const 0, ?_, ?_⟩ <;> simp
  add_mem' := by
    rintro K P ⟨σK, NK, NKd, hNK, hNKd, hK, hKE⟩ ⟨σP, NP, NPd, hNP, hNPd, hP, hPE⟩
    refine ⟨max σK σP, NK + NP, NKd + NPd, hNK.add hNP, hNKd.add hNPd, ?_, ?_⟩
    · intro s hs
      obtain ⟨hK₁, hK₂, hK₃, hK₄⟩ := hK s ((le_max_left _ _).trans_lt hs)
      obtain ⟨hP₁, hP₂, hP₃, hP₄⟩ := hP s ((le_max_right _ _).trans_lt hs)
      refine ⟨hK₁.add hP₁, hK₂.add hP₂, ?_, ?_⟩
      · simp only [Prod.fst_add, Pi.add_apply, hK₃, hP₃, integral_add hK₁ hP₁, mul_add]
      · simp only [Prod.snd_add, Pi.add_apply, hK₄, hP₄, integral_add hK₂ hP₂, mul_add]
    · intro s
      simp only [Pi.add_apply, hKE s, hPE s, mul_add]
  smul_mem' := by
    rintro c K ⟨σ, N, Nd, hN, hNd, hK, hE⟩
    refine ⟨σ, c • N, c • Nd, hN.const_mul c, hNd.const_mul c, ?_, ?_⟩
    · intro s hs
      obtain ⟨hK₁, hK₂, hK₃, hK₄⟩ := hK s hs
      refine ⟨hK₁.const_mul c, hK₂.const_mul c, ?_, ?_⟩
      · change c * N s = L s * (∫ x, c * K.1 s x ∂μ)
        rw [hK₃, integral_const_mul]
        ring
      · change c * Nd s = Ld s * (∫ y, c * K.2 s y ∂ν)
        rw [hK₄, integral_const_mul]
        ring
    · intro s
      simp only [Pi.smul_apply, smul_eq_mul, hE s]
      ring

private def complexUnequalKernelPair {r t : ℕ} (h : t < r) :
    (Langlands.GeneralLinear (r + 1) ℂ → ℂ) →ₗ[ℂ]
      (Langlands.GeneralLinear (t + 1) ℂ → ℂ) →ₗ[ℂ]
      ((ℂ → LeftUnipotentQuotient t ℂ → ℂ) ×
        (ℂ → LeftUnipotentQuotient t ℂ × Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℂ → ℂ)) :=
  LinearMap.mk₂ ℂ (fun W W' => (complexUnequalIntegrand h W W', complexUnequalDualKernel h W W'))
    (by
      intros
      apply Prod.ext <;> funext s x
      · simp [complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand, add_mul]
      · simp [complexUnequalDualKernel, blockKernel, ArchimedeanLocal.translateFunction,
          ArchimedeanLocal.dualFunction, add_mul])
    (by
      intros
      apply Prod.ext <;> funext s x
      · simp [complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand, mul_assoc]
      · simp [complexUnequalDualKernel, blockKernel, ArchimedeanLocal.translateFunction,
          ArchimedeanLocal.dualFunction, mul_assoc])
    (by
      intros
      apply Prod.ext <;> funext s x
      · simp [complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand, mul_add, add_mul]
      · simp [complexUnequalDualKernel, blockKernel, ArchimedeanLocal.translateFunction,
          ArchimedeanLocal.dualFunction, mul_add, add_mul])
    (by
      intros
      apply Prod.ext <;> funext s x
      · simp [complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand]
        ring
      · simp [complexUnequalDualKernel, blockKernel, ArchimedeanLocal.translateFunction,
          ArchimedeanLocal.dualFunction]
        ring)

private theorem complexWhittakerModel_le_of_values {n : ℕ} {d : List ComplexCharacterData}
    {a : ℂˣ} {S : Submodule ℂ (Langlands.GeneralLinear (n + 1) ℂ → ℂ)}
    (hS : ∀ B, IsComplexWhittakerIntertwiner n d a B → ∀ f, B f ∈ S) :
    complexWhittakerModel n d a ≤ S := by
  apply iSup_le
  intro B
  apply iSup_le
  intro hB
  rintro _ ⟨f, rfl⟩
  exact hS B hB f

private theorem complexLFactor_denominator_ne_on_right (ds : List ComplexCharacterData) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → (complexLFactor ds).denominator s ≠ 0 := by
  induction ds with
  | nil => exact ⟨0, fun _ _ => one_ne_zero⟩
  | cons d ds ih =>
    obtain ⟨σ, hσ⟩ := ih
    let shift : ℂ := d.exponent + (d.weight.natAbs : ℂ) / 2
    refine ⟨max σ (-shift.re), fun s hs => ?_⟩
    rw [complexLFactor_cons, ReciprocalEntire.denominator_mul]
    refine mul_ne_zero (fun hzero => ?_) (hσ s ((le_max_left _ _).trans_lt hs))
    have hs' : -shift.re < s.re := (le_max_right _ _).trans_lt hs
    obtain ⟨m, hm⟩ := (d.lFactor_isPole s).mp hzero
    have hm' : (s + shift).re = (-(m : ℂ)).re := congrArg Complex.re hm
    simp only [Complex.add_re, Complex.neg_re, Complex.natCast_re] at hm'
    linarith [Nat.cast_nonneg (α := ℝ) m]

private theorem meromorphicOn_unnormalize (F : ReciprocalEntire) {N : ℂ → ℂ}
    (hN : Differentiable ℂ N) : MeromorphicOn (fun s => N s * (F.denominator s)⁻¹) Set.univ :=
  fun s _ => (hN.analyticAt s).meromorphicAt.mul (F.entire.analyticAt s).meromorphicAt.inv

/-! ### Open premises and verified implication -/

/-- Absolute convergence on a right half-plane for the ordinary and dual kernels
on pairs of values of Whittaker intertwiners. The dual measure is the product measure. -/
def ComplexUnequalIntertwinerConvergenceStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (d d' : List ComplexCharacterData),
    d.length = r + 1 → d'.length = t + 1 →
  ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData t)
    (B : Automorphic.complexStandardKFinite (r + 1) d →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℂ → ℂ))
    (B' : Automorphic.complexStandardKFinite (t + 1) d' →ₗ[ℂ]
      (Langlands.GeneralLinear (t + 1) ℂ → ℂ)),
    IsComplexWhittakerIntertwiner r d a B → IsComplexWhittakerIntertwiner t d' (-a) B' →
  ∀ f f', ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
    Integrable (complexUnequalIntegrand h (B f) (B' f') s) D.measure ∧
    Integrable (complexUnequalDualKernel h (B f) (B' f') s)
      (complexUnequalDualMeasure (r := r) a D)

/-- Entire continuations of the normalized ordinary and dual integrals on pairs
of intertwiner values, with the normalized functional equation. The normalization
multiplies by the denominator of the respective reciprocal Gamma product. -/
def ComplexUnequalNormalizedIntertwinerEquationStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (d d' : List ComplexCharacterData),
    d.length = r + 1 → d'.length = t + 1 →
  ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData t)
    (B : Automorphic.complexStandardKFinite (r + 1) d →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℂ → ℂ))
    (B' : Automorphic.complexStandardKFinite (t + 1) d' →ₗ[ℂ]
      (Langlands.GeneralLinear (t + 1) ℂ → ℂ)),
    IsComplexWhittakerIntertwiner r d a B → IsComplexWhittakerIntertwiner t d' (-a) B' →
  ∀ f f', ∃ (σ : ℝ) (N Nd : ℂ → ℂ),
    Differentiable ℂ N ∧ Differentiable ℂ Nd ∧
    (∀ s : ℂ, σ < s.re →
      N s = (complexPairLFactor d d').denominator s *
        complexUnequalIntegral h D (B f) (B' f') s ∧
      Nd s = (complexPairLFactor (d.map ComplexCharacterData.inv)
        (d'.map ComplexCharacterData.inv)).denominator s *
        complexUnequalDualIntegral h a D (B f) (B' f') s) ∧
    ∀ s : ℂ, Nd (1 - s) =
      complexCentralSign d' ^ r *
        (complexPairEpsilon d d' a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ) * N s

/-- The two statements on intertwiner values imply the local unequal-rank statement
on the full complex Whittaker models. -/
def ComplexUnequalAnalyticReductionStatement : Prop :=
  ComplexUnequalIntertwinerConvergenceStatement →
  ComplexUnequalNormalizedIntertwinerEquationStatement →
  ComplexLocalUnequalFunctionalEquationStatement

theorem complexUnequalAnalyticReduction : ComplexUnequalAnalyticReductionStatement := by
  intro hconv hnormal r t h d d' hd hd' a D W W' hW hW'
  let F := complexPairLFactor d d'
  let Fd := complexPairLFactor (d.map ComplexCharacterData.inv) (d'.map ComplexCharacterData.inv)
  let E (s : ℂ) := complexCentralSign d' ^ r *
    (complexPairEpsilon d d' a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ)
  let K := complexUnequalKernelPair h
  let S := normalizedKernelPairs D.measure (complexUnequalDualMeasure (r := r) a D)
    F.denominator Fd.denominator E
  have hgen (B B') (hB : IsComplexWhittakerIntertwiner r d a B)
      (hB' : IsComplexWhittakerIntertwiner t d' (-a) B') (f f') :
      K (B f) (B' f') ∈ S := by
    obtain ⟨σ, hσ⟩ := hconv r t h d d' hd hd' a D B B' hB hB' f f'
    obtain ⟨τ, N, Nd, hN, hNd, hright, hE⟩ :=
      hnormal r t h d d' hd hd' a D B B' hB hB' f f'
    refine ⟨max σ τ, N, Nd, hN, hNd, ?_, hE⟩
    intro s hs
    obtain ⟨hint, hintd⟩ := hσ s ((le_max_left _ _).trans_lt hs)
    obtain ⟨hN', hNd'⟩ := hright s ((le_max_right _ _).trans_lt hs)
    rw [complexUnequalDualIntegral_eq_prod h a D (B f) (B' f') s hintd] at hNd'
    exact ⟨hint, hintd, hN', hNd'⟩
  have hwhole : complexWhittakerModel r d a ≤ S.comap (K.flip W') := by
    apply complexWhittakerModel_le_of_values
    intro B hB f
    have hsub : complexWhittakerModel t d' (-a) ≤ S.comap (K (B f)) := by
      apply complexWhittakerModel_le_of_values
      intro B' hB' f'
      exact hgen B B' hB hB' f f'
    exact hsub hW'
  have hmem : K W W' ∈ S := hwhole hW
  obtain ⟨σ, N, Nd, hN, hNd, hright, hE⟩ := hmem
  obtain ⟨σF, hσF⟩ := complexLFactor_denominator_ne_on_right (complexPairBlocks d d')
  obtain ⟨σFd, hσFd⟩ := complexLFactor_denominator_ne_on_right
    (complexPairBlocks (d.map ComplexCharacterData.inv) (d'.map ComplexCharacterData.inv))
  let τ := max σ (max σF σFd)
  have hσ {s : ℂ} (hs : τ < s.re) : σ < s.re := (le_max_left _ _).trans_lt hs
  have hF {s : ℂ} (hs : τ < s.re) : F.denominator s ≠ 0 :=
    hσF s ((le_trans (le_max_left σF σFd) (le_max_right σ _)).trans_lt hs)
  have hFd {s : ℂ} (hs : τ < s.re) : Fd.denominator s ≠ 0 :=
    hσFd s ((le_trans (le_max_right σF σFd) (le_max_right σ _)).trans_lt hs)
  have hI (s : ℂ) (hs : τ < s.re) :
      Integrable (complexUnequalIntegrand h W W' s) D.measure := (hright s (hσ hs)).1
  have hId (s : ℂ) (hs : τ < s.re) :
      Integrable (complexUnequalDualKernel h W W' s) (complexUnequalDualMeasure (r := r) a D) :=
    (hright s (hσ hs)).2.1
  refine ⟨τ, fun s => N s * (F.denominator s)⁻¹, fun s => Nd s * (Fd.denominator s)⁻¹, hI, hId,
    differentiableOn_complexUnequalIntegral h D W W' hI,
    differentiableOn_complexUnequalDualIntegral h a D W W' hId,
    meromorphicOn_unnormalize F hN, meromorphicOn_unnormalize Fd hNd, ?_, ?_, ?_⟩
  · intro s hs
    change _ = N s * (F.denominator s)⁻¹
    have hN' : N s = F.denominator s * complexUnequalIntegral h D W W' s :=
      (hright s (hσ hs)).2.2.1
    rw [hN', mul_comm (F.denominator s), mul_assoc, mul_inv_cancel₀ (hF hs), mul_one]
  · intro s hs
    change _ = Nd s * (Fd.denominator s)⁻¹
    have hNd' : Nd s = Fd.denominator s *
        (∫ p, complexUnequalDualKernel h W W' s p ∂complexUnequalDualMeasure (r := r) a D) :=
      (hright s (hσ hs)).2.2.2
    rw [← complexUnequalDualIntegral_eq_prod h a D W W' s (hId s hs)] at hNd'
    rw [hNd', mul_comm (Fd.denominator s), mul_assoc, mul_inv_cancel₀ (hFd hs), mul_one]
  · filter_upwards with s
    change (F.denominator s)⁻¹ * (Nd (1 - s) * (Fd.denominator (1 - s))⁻¹) =
      E s * (Fd.denominator (1 - s))⁻¹ * (N s * (F.denominator s)⁻¹)
    rw [hE s]
    ring

end Langlands.Global.RankinSelbergGlobal
