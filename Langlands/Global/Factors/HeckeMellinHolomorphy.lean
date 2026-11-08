import Langlands.Global.Factors.HeckeFiniteMellin
import Langlands.Global.Factors.HeckeEpsilonProduct
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! # Holomorphy of the actual finite Hecke Mellin series -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open Filter Topology

namespace Langlands.Global.HeckeFunctionalEquation

open NumberField
open Langlands.HarmonicAnalysis
open Langlands.LocalFactor.PadicAbelian
open Langlands.Global.CompletionPadic
open HeckeDivisorEulerProduct

variable {K : Type u} [Field K] [NumberField K]

/-- The logarithmic spectral slope of an actual finite Mellin divisor coefficient. -/
def finiteMellinLogSlope (d : FinitePlace K →₀ ℤ) : ℂ :=
  ∑ v ∈ d.support, -(d v : ℂ) *
    (Real.log ((topologicalData v).residueCardinality : ℝ) : ℂ)

theorem shellWeight_eq_zero_mul_exp (χ : HeckeCharacter K) (v : FinitePlace K)
    (s : ℂ) (k : ℤ) :
    shellWeight χ v s k = shellWeight χ v 0 k *
      Complex.exp ((-(k : ℂ) *
        (Real.log ((topologicalData v).residueCardinality : ℝ) : ℂ)) * s) := by
  rw [shellWeight, shellMellinTerm_eq_exp, shellWeight, shellMellinTerm_eq_exp]
  simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one]
  congr 1
  congr 1
  ring

/-- Each actual divisor coefficient is a single exponential times its value at zero. -/
theorem finiteMellin_coefficient_eq_zero_mul_exp (χ : HeckeCharacter K)
    (d : FinitePlace K →₀ ℤ) (s : ℂ) :
    DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ v s) d =
      DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ v 0) d *
        Complex.exp (finiteMellinLogSlope d * s) := by
  classical
  simp only [DivisorEulerProduct.coefficient, Finset.empty_union, finiteMellinLogSlope]
  calc
    (∏ v ∈ d.support, shellWeight χ v s (d v)) =
        ∏ v ∈ d.support, shellWeight χ v 0 (d v) *
          Complex.exp ((-(d v : ℂ) *
            (Real.log ((topologicalData v).residueCardinality : ℝ) : ℂ)) * s) :=
      Finset.prod_congr rfl (fun v _ => shellWeight_eq_zero_mul_exp χ v s (d v))
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.sum_mul, Complex.exp_sum]

theorem hasDerivAt_finiteMellin_coefficient (χ : HeckeCharacter K)
    (d : FinitePlace K →₀ ℤ) (s : ℂ) :
    HasDerivAt (fun z => DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ v z) d)
      (finiteMellinLogSlope d *
        DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ v s) d) s := by
  have he := funext (finiteMellin_coefficient_eq_zero_mul_exp χ d)
  have h := (((hasDerivAt_id s).const_mul (finiteMellinLogSlope d)).cexp).const_mul
    (DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ v 0) d)
  simp only [id_eq, mul_one] at h
  rw [← he] at h
  exact h.congr_deriv (by rw [finiteMellin_coefficient_eq_zero_mul_exp χ d s]; ring)

/-- Increasing the real part decreases each actual Euler-test shell norm. -/
theorem norm_shellWeight_le_of_re_le (χ : HeckeCharacter K) (v : FinitePlace K)
    {s t : ℂ} (hst : t.re ≤ s.re) (k : ℤ) :
    ‖shellWeight χ v s k‖ ≤ ‖shellWeight χ v t k‖ := by
  classical
  have hg : ‖geometricCoefficient χ v s‖ ≤ ‖geometricCoefficient χ v t‖ := by
    unfold geometricCoefficient
    rw [norm_mul, norm_mul, HeckeEulerProduct.norm_spectralVariable,
      HeckeEulerProduct.norm_spectralVariable]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le)
      (neg_le_neg hst)
  by_cases hc : (topologicalData v).multiplicativeConductor (χ.finiteComponent v) = 0
  · rw [shellWeight, shellMellinTerm,
      eulerTest_uniformizer_pow_unramified (topologicalData v) _ hc,
      shellWeight, shellMellinTerm,
      eulerTest_uniformizer_pow_unramified (topologicalData v) _ hc]
    by_cases hk : 0 ≤ k
    · simp only [ite_eq_left hk, one_mul, norm_zpow]
      exact zpow_le_zpow_left₀ hk (norm_nonneg _) hg
    · simp only [ite_eq_right hk, zero_mul, norm_zero, le_refl]
  · rw [shellWeight, shellMellinTerm,
      eulerTest_uniformizer_pow_ramified (topologicalData v) _ hc,
      shellWeight, shellMellinTerm,
      eulerTest_uniformizer_pow_ramified (topologicalData v) _ hc]
    by_cases hk : k = 0 <;> simp [hk]

/-- The actual divisor coefficients have the same monotonicity. -/
theorem norm_finiteMellin_coefficient_le_of_re_le (χ : HeckeCharacter K)
    {s t : ℂ} (hst : t.re ≤ s.re) (d : FinitePlace K →₀ ℤ) :
    ‖DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ v s) d‖ ≤
      ‖DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ v t) d‖ := by
  classical
  simp only [DivisorEulerProduct.coefficient, Finset.empty_union, norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    (fun v _ => norm_shellWeight_le_of_re_le χ v hst (d v))

/-- Absolute convergence at a real parameter gives uniform convergence on the
closed half-plane to its right. -/
theorem tendstoUniformlyOn_finiteMellin (χ : HeckeCharacter K) (t : ℝ)
    (ht : Summable (fun d : FinitePlace K →₀ ℤ =>
      ‖DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ v (t : ℂ)) d‖)) :
    TendstoUniformlyOn
      (fun D : Finset (FinitePlace K →₀ ℤ) => fun s : ℂ =>
        ∑ d ∈ D, DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ v s) d)
      (finiteMellin χ) atTop {s : ℂ | t ≤ s.re} := by
  exact tendstoUniformlyOn_tsum ht (fun d s hs =>
    norm_finiteMellin_coefficient_le_of_re_le χ (t := (t : ℂ)) hs d)

/-- The dominated actual divisor series is holomorphic on the open half-plane. -/
theorem differentiableOn_finiteMellin (χ : HeckeCharacter K) (t : ℝ)
    (ht : Summable (fun d : FinitePlace K →₀ ℤ =>
      ‖DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ v (t : ℂ)) d‖)) :
    DifferentiableOn ℂ (finiteMellin χ) {s : ℂ | t < s.re} := by
  exact Complex.differentiableOn_tsum_of_summable_norm ht
    (fun d s _ => (hasDerivAt_finiteMellin_coefficient χ d s).differentiableAt.differentiableWithinAt)
    (isOpen_lt continuous_const Complex.continuous_re)
    (fun d s hs => norm_finiteMellin_coefficient_le_of_re_le χ (t := (t : ℂ)) hs.le d)

/-- Termwise differentiation is justified by local uniform convergence, with
the actual logarithmic coefficient slopes. -/
theorem hasSum_finiteMellin_derivative (χ : HeckeCharacter K) (t : ℝ)
    (ht : Summable (fun d : FinitePlace K →₀ ℤ =>
      ‖DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ v (t : ℂ)) d‖))
    {s : ℂ} (hs : t < s.re) :
    HasSum (fun d : FinitePlace K →₀ ℤ =>
      finiteMellinLogSlope d *
        DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ v s) d)
      (deriv (finiteMellin χ) s) := by
  have h := Complex.hasSum_deriv_of_summable_norm ht
    (fun d z _ => (hasDerivAt_finiteMellin_coefficient χ d z).differentiableAt.differentiableWithinAt)
    (isOpen_lt continuous_const Complex.continuous_re)
    (fun d z hz => norm_finiteMellin_coefficient_le_of_re_le χ (t := (t : ℂ)) hz.le d) hs
  simp only [(hasDerivAt_finiteMellin_coefficient χ _ _).deriv] at h
  convert h using 1
  rfl

/-- A common right half-plane has uniform convergence, holomorphy, a
holomorphic reciprocal and a nonzero exact Euler-product value. -/
theorem exists_finiteMellin_analytic_halfPlane (χ : HeckeCharacter K) :
    ∃ σ : ℝ,
      TendstoUniformlyOn
        (fun D : Finset (FinitePlace K →₀ ℤ) => fun s : ℂ =>
          ∑ d ∈ D, DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ v s) d)
        (finiteMellin χ) atTop {s : ℂ | σ ≤ s.re} ∧
      DifferentiableOn ℂ (finiteMellin χ) {s : ℂ | σ < s.re} ∧
      DifferentiableOn ℂ (fun s => (finiteMellin χ s)⁻¹) {s : ℂ | σ < s.re} ∧
      ∀ s : ℂ, σ < s.re →
        Summable (fun d : FinitePlace K →₀ ℤ =>
          ‖DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ v s) d‖) ∧
        HasProd (fun v => lFactor (topologicalData v) (χ.finiteComponent v) s)
          (finiteMellin χ s) ∧
        finiteMellin χ s ≠ 0 := by
  obtain ⟨σc, hc⟩ := exists_finiteMellin_hasProd χ
  obtain ⟨σe, he⟩ := HeckeEulerProduct.exists_hasProd_lFactor χ
  let σ := max (σc + 1) σe
  have hσc : σc < σ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have ht := (hc (σ : ℂ) (by simpa using hσc)).1
  have hd := differentiableOn_finiteMellin χ σ ht
  have hn : ∀ s : ℂ, σ < s.re → finiteMellin χ s ≠ 0 := by
    intro s hs
    obtain ⟨L, hL, hprod⟩ := he s (lt_of_le_of_lt (le_max_right _ _) hs)
    have hp := (hc s (hσc.trans hs)).2
    exact hp.unique hprod ▸ hL
  refine ⟨σ, tendstoUniformlyOn_finiteMellin χ σ ht, hd, hd.inv hn, ?_⟩
  intro s hs
  exact ⟨(hc s (hσc.trans hs)).1, (hc s (hσc.trans hs)).2, hn s hs⟩

/-- Both actual finite series and the Fourier finite series are holomorphic and
nonvanishing on one right half-plane, with the exact actual epsilon factor. -/
theorem exists_finiteMellin_common_analytic_halfPlane (χ : HeckeCharacter K)
    (ψ : UnitaryAdditiveCharacter (Adeles K))
    (hdiag : ∀ x : K, ψ (diagonal K x) = 1)
    (ψf : ∀ v : FinitePlace K,
      @UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (topologicalData v).topology)
    (hf : ∀ v, IsFiniteAdditiveComponent ψ v (ψf v))
    (μ : ∀ v : FinitePlace K, SelfDualHaar (topologicalData v) (ψf v))
    (aR : {v : InfinitePlace K // v.IsReal} → ℝˣ)
    (hR : ∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v))
    (aC : {v : InfinitePlace K // v.IsComplex} → ℂˣ)
    (hC : ∀ v, IsComplexAdditiveComponent ψ v.1 v.2 (aC v)) :
    ∃ (σ : ℝ) (S : Finset (FinitePlace K)),
      (∀ v ∉ S, ∀ s : ℂ, fourierShellWeight χ ψf μ v s 0 = 1) ∧
      (∀ v ∉ S, ∀ s : ℂ, finiteEpsilon χ ψf μ v s = 1) ∧
      DifferentiableOn ℂ (finiteMellin χ) {s : ℂ | σ < s.re} ∧
      DifferentiableOn ℂ (finiteMellin χ⁻¹) {s : ℂ | σ < s.re} ∧
      DifferentiableOn ℂ (fourierFiniteMellin χ ψf μ S) {s : ℂ | σ < s.re} ∧
      DifferentiableOn ℂ (fun s => (fourierFiniteMellin χ ψf μ S s)⁻¹)
        {s : ℂ | σ < s.re} ∧
      ∀ s : ℂ, σ < s.re →
        finiteMellin χ s ≠ 0 ∧ finiteMellin χ⁻¹ s ≠ 0 ∧
        fourierFiniteMellin χ ψf μ S s ≠ 0 ∧
        fourierFiniteMellin χ ψf μ S s =
          finiteGlobalEpsilon χ ψf μ (1 - s) * finiteMellin χ⁻¹ s := by
  obtain ⟨σ₀, S, hz, hε, hcommon⟩ :=
    exists_finiteMellin_common_halfPlane χ ψ hdiag ψf hf μ aR hR aC hC
  obtain ⟨σ₁, _, hd₁, _, hval₁⟩ := exists_finiteMellin_analytic_halfPlane χ
  obtain ⟨σ₂, _, hd₂, _, hval₂⟩ := exists_finiteMellin_analytic_halfPlane χ⁻¹
  let σ := max σ₀ (max σ₁ σ₂)
  have h₀ : ∀ {s : ℂ}, σ < s.re → σ₀ < s.re :=
    fun hs => lt_of_le_of_lt (le_max_left _ _) hs
  have h₁ : ∀ {s : ℂ}, σ < s.re → σ₁ < s.re :=
    fun hs => lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hs
  have h₂ : ∀ {s : ℂ}, σ < s.re → σ₂ < s.re :=
    fun hs => lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hs
  have heq : ∀ s : ℂ, σ < s.re → fourierFiniteMellin χ ψf μ S s =
      finiteGlobalEpsilon χ ψf μ (1 - s) * finiteMellin χ⁻¹ s := by
    intro s hs
    obtain ⟨_, _, _, _, _, _, h⟩ := hcommon s (h₀ hs)
    rwa [finiteGlobalEpsilon_eq_prod χ ψf μ S hε (1 - s)]
  have hdε : Differentiable ℂ (fun s : ℂ => finiteGlobalEpsilon χ ψf μ (1 - s)) :=
    (finiteGlobalEpsilon_differentiable χ ψf μ ψ hdiag hf aR hR aC hC).comp
      ((differentiable_const (1 : ℂ)).sub differentiable_id)
  have hdf : DifferentiableOn ℂ (fourierFiniteMellin χ ψf μ S) {s : ℂ | σ < s.re} :=
    (hdε.differentiableOn.mul (hd₂.mono (fun _ hs => h₂ hs))).congr heq
  have hnf : ∀ s : ℂ, σ < s.re → fourierFiniteMellin χ ψf μ S s ≠ 0 := by
    intro s hs
    rw [heq s hs]
    exact mul_ne_zero (finiteGlobalEpsilon_ne_zero χ ψf μ ψ hdiag hf aR hR aC hC (1 - s))
      (hval₂ s (h₂ hs)).2.2
  refine ⟨σ, S, hz, hε, hd₁.mono (fun _ hs => h₁ hs),
    hd₂.mono (fun _ hs => h₂ hs), hdf, hdf.inv hnf, fun s hs => ?_⟩
  exact ⟨(hval₁ s (h₁ hs)).2.2, (hval₂ s (h₂ hs)).2.2, hnf s hs, heq s hs⟩

end Langlands.Global.HeckeFunctionalEquation
