import Langlands.Global.RankinSelberg.ComplexSquareConvolutionDerivative
import Langlands.Global.RankinSelberg.ComplexGodementContinuedModel

/-! # Spanning by normalized square Gaussian convolutions -/

noncomputable section

open Filter MeasureTheory Set
open scoped Matrix.Norms.Operator SchwartzMap TensorProduct Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal Langlands.Archimedean Langlands.Automorphic Langlands.GeneralLinear
open Langlands.LocalFactor.Archimedean
open ComplexGodementGaussianPolynomial (Coordinates)
open ComplexGodement (characterWeight normPower determinantSlope hasDerivAt_rightDerivative_exponential)
open ComplexMaximalParabolicIntegration (normSqC normSqC_det_unitary)
open ComplexSquareZeta (squarePolynomialGaussian exists_left_squarePolynomialGaussian
  exists_schwartz_squarePolynomialGaussian squareDirectionalTest complexSquareGaussianDerivative)

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel

variable {r : ℕ}
local notation "n" => (r + 1 : ℕ)
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "K" => Matrix.unitaryGroup (Fin n) ℂ
local notation "KU" => unitaryCompact ℂ n
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "KF[" e "]" => complexStandardKFinite n (List.ofFn e)
local notation "Poly" => MvPolynomial (Coordinates n n) ℂ

/-- The polynomial normalization of square convolution as evaluated in a Whittaker realization. -/
def HasSquareConvolutionTrace (μ : Measure G) (d : ComplexCharacterData)
    (e : Fin n → ComplexCharacterData) (B : KF[e] →ₗ[ℂ] (G → ℂ))
    (Φ : 𝓢(Mat, ℂ)) (f : KF[e]) (F : ℂ → KF[e]) : Prop :=
  (∃ (l : ℕ) (p : Fin l → Polynomial ℂ) (v : Fin l → KF[e]),
    ∀ s, F s = ∑ j, (p j).eval s • v j) ∧
  (∃ σ : ℝ, ∀ (s : ℂ), σ < s.re → ∀ x : G,
    B (F s) x = (complexPairLFactor [d] (List.ofFn e)).denominator s *
      ∫ g, complexJacquetMatrixIntegrand d (fun g => B f (x * g)) Φ s g ∂μ)

/-- Span of the values at one spectral point of all standard square Gaussian convolutions. -/
def squareConvolutionSpan (μ : Measure G) (d : ComplexCharacterData) (e : Fin n → ComplexCharacterData)
    (B : KF[e] →ₗ[ℂ] (G → ℂ)) (s₀ : ℂ) : Submodule ℂ KF[e] :=
  Submodule.span ℂ {v | ∃ (Φ : 𝓢(Mat, ℂ)) (P : Poly) (f : KF[e]) (F : ℂ → KF[e]),
    (Φ : Mat → ℂ) = squarePolynomialGaussian P ∧ HasSquareConvolutionTrace μ d e B Φ f F ∧ F s₀ = v}

/-- The value of a polynomial square Gaussian convolution belongs to the convolution span. -/
theorem mem_squareConvolutionSpan {μ : Measure G} {d : ComplexCharacterData} {e : Fin n → ComplexCharacterData}
    {B : KF[e] →ₗ[ℂ] (G → ℂ)} {s₀ : ℂ} {Φ : 𝓢(Mat, ℂ)} {P : Poly} {f : KF[e]} {F : ℂ → KF[e]}
    (hΦ : (Φ : Mat → ℂ) = squarePolynomialGaussian P) (hF : HasSquareConvolutionTrace μ d e B Φ f F) :
    F s₀ ∈ squareConvolutionSpan μ d e B s₀ :=
  Submodule.subset_span ⟨Φ, P, f, F, hΦ, hF, rfl⟩

private theorem differentiable_trace_evaluation {μ : Measure G} {d : ComplexCharacterData}
    {e : Fin n → ComplexCharacterData} {B : KF[e] →ₗ[ℂ] (G → ℂ)}
    {Φ : 𝓢(Mat, ℂ)} {f : KF[e]} {F : ℂ → KF[e]}
    (hF : HasSquareConvolutionTrace μ d e B Φ f F) (b : KF[e] →ₗ[ℂ] ℂ) :
    Differentiable ℂ (fun s => b (F s)) := by
  obtain ⟨l, p, v, h⟩ := hF.1
  simp_rw [h, map_sum, map_smul, smul_eq_mul]
  exact fun s => DifferentiableAt.fun_sum fun j _ => (p j).differentiable.differentiableAt.mul_const _

private theorem entire_eq_of_right {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    {σ : ℝ} (h : ∀ s : ℂ, σ < s.re → f s = g s) : f = g := by
  let s : ℂ := ((σ + 1 : ℝ) : ℂ)
  apply AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => hf.analyticAt z) (fun z _ => hg.analyticAt z) (z₀ := s)
  have hnear : ∀ᶠ z : ℂ in 𝓝 s, σ < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num [s])
  exact hnear.mono h

private theorem integrand_eq_weight (d : ComplexCharacterData) (b : G → ℂ) (Φ : Mat → ℂ)
    (s : ℂ) (g : G) : complexJacquetMatrixIntegrand d b Φ s g =
      Φ g.val * (characterWeight d (s + (r : ℂ) / 2) (determinant g) * b g) := by
  rw [complexJacquetMatrixIntegrand, square_detPower_eq_normPower]
  change _ = Φ g.val * (((d.character (determinant g) : ℂ) * normPower _ (determinant g)) * b g)
  ring

private theorem trace_generator_compact (μ : Measure G) [μ.IsHaarMeasure]
    (d : ComplexCharacterData) (e : Fin n → ComplexCharacterData) (a : ℂˣ)
    (B : KF[e] →ₗ[ℂ] (G → ℂ)) (hB : IsComplexWhittakerIntertwiner r (List.ofFn e) a B)
    (hInj : Function.Injective B) (s₀ : ℂ) (k : K) (Φ : 𝓢(Mat, ℂ)) (P : Poly)
    (hΦ : (Φ : Mat → ℂ) = squarePolynomialGaussian P) (f : KF[e]) (F : ℂ → KF[e])
    (hF : HasSquareConvolutionTrace μ d e B Φ f F) :
    complexStandardRep n (List.ofFn e) k (F s₀) ∈ squareConvolutionSpan μ d e B s₀ := by
  let k₀ : KU := ⟨Unitary.toUnits k, k.2⟩
  let T := complexStandardRep n (List.ofFn e) k
  obtain ⟨Q, _, hQ⟩ := exists_left_squarePolynomialGaussian P k₀
  obtain ⟨Ψ, hΨ⟩ := exists_schwartz_squarePolynomialGaussian Q
  obtain ⟨V, hVpoly, hVTrace⟩ := complexSquareZetaConvolution μ d e Ψ Q hΨ a B hB f
  have hV : HasSquareConvolutionTrace μ d e B Ψ f V := ⟨hVpoly.1, hVTrace⟩
  obtain ⟨σ, hσ⟩ := hF.2
  obtain ⟨τ, hτ⟩ := hVTrace
  let c : ℂ := d.character (determinant k₀.val⁻¹)
  have hc (s : ℂ) : characterWeight d (s + (r : ℂ) / 2) (determinant k₀.val⁻¹) = c := by
    change c * normSqC k₀.val⁻¹.val.det ^ (s + (r : ℂ) / 2) = c
    have h := normSqC_det_unitary k₀⁻¹
    change normSqC k₀.val⁻¹.val.det = 1 at h
    rw [h, Complex.one_cpow, mul_one]
  have hEq (x : G) : (fun s => B (T (F s)) x) = fun s => c * B (V s) x := by
    let ev := (LinearMap.proj x).comp B
    refine entire_eq_of_right (differentiable_trace_evaluation hF (ev.comp T))
      ((differentiable_trace_evaluation hV ev).const_mul c) (σ := max σ τ) ?_
    intro s hs
    rw [hB.2.2.2.1 k₀ (F s) (T (F s)) rfl]
    change B (F s) (x * k₀.val) = _
    rw [hσ s ((le_max_left σ τ).trans_lt hs), hτ s ((le_max_right σ τ).trans_lt hs),
      squareConvolution_leftShear μ d s Φ (B f) x k₀.val, hc]
    have he (g : G) : Φ (k₀.val⁻¹.val * g.val) *
          (characterWeight d (s + (r : ℂ) / 2) (determinant g) * B f (x * g)) =
        complexJacquetMatrixIntegrand d (fun g => B f (x * g)) Ψ s g := by
      rw [integrand_eq_weight, hΦ, hΨ, hQ]
    simp_rw [he]
    ring
  have he : T (F s₀) = c • V s₀ := by
    apply hInj
    funext x
    simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using congrFun (hEq x) s₀
  rw [he]
  exact (squareConvolutionSpan μ d e B s₀).smul_mem c (mem_squareConvolutionSpan hΨ hV)

private theorem trace_generator_lie (μ : Measure G) [μ.IsHaarMeasure]
    (d : ComplexCharacterData) (e : Fin n → ComplexCharacterData) (a : ℂˣ)
    (B : KF[e] →ₗ[ℂ] (G → ℂ)) (hB : IsComplexWhittakerIntertwiner r (List.ofFn e) a B)
    (hInj : Function.Injective B) (s₀ : ℂ) (X : Mat) (Φ : 𝓢(Mat, ℂ)) (P : Poly)
    (hΦ : (Φ : Mat → ℂ) = squarePolynomialGaussian P) (f : KF[e]) (F : ℂ → KF[e])
    (hF : HasSquareConvolutionTrace μ d e B Φ f F) :
    complexStandardLie n (List.ofFn e) (1 ⊗ₜ[ℝ] X) (F s₀) ∈ squareConvolutionSpan μ d e B s₀ := by
  let T := complexStandardLie n (List.ofFn e) (1 ⊗ₜ[ℝ] X)
  let A := squareLeftMultiply (-X)
  let Ψ := squareDirectionalTest A Φ
  obtain ⟨Q, hΨ⟩ := complexSquareGaussianDerivative A Φ P hΦ
  obtain ⟨V, hVpoly, hVTrace⟩ := complexSquareZetaConvolution μ d e Ψ Q hΨ a B hB f
  have hV : HasSquareConvolutionTrace μ d e B Ψ f V := ⟨hVpoly.1, hVTrace⟩
  obtain ⟨σ, hσ⟩ := hF.2
  obtain ⟨τ, hτ⟩ := hVTrace
  obtain ⟨C, M, hM⟩ := hB.2.2.1 f
  let C₀ := max C 0
  have hC₀ : 0 ≤ C₀ := le_max_right _ _
  have hb (g : G) : ‖B f g‖ ≤ C₀ * complexMatrixHeight g ^ M :=
    (hM g).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (complexMatrixHeight_nonneg g) _))
  let b : ℝ := (n : ℝ) + M - (d.exponent + (r : ℂ) / 2).re
  let β (s : ℂ) := determinantSlope d (s + (r : ℂ) / 2) (-X)
  let L (s : ℂ) := (complexPairLFactor [d] (List.ofFn e)).denominator s
  have hEq (x : G) : (fun s => B (T (F s)) x) = fun s => β s * B (F s) x + B (V s) x := by
    let ev := (LinearMap.proj x).comp B
    have hdβ : Differentiable ℂ β := (differentiable_determinantSlope d (-X)).comp (differentiable_id.add_const _)
    refine entire_eq_of_right (differentiable_trace_evaluation hF (ev.comp T))
      ((hdβ.mul (differentiable_trace_evaluation hF ev)).add (differentiable_trace_evaluation hV ev))
      (σ := max b (max σ τ)) ?_
    intro s hs
    have hsσ := (le_max_left σ τ).trans_lt ((le_max_right b _).trans_lt hs)
    have hsτ := (le_max_right σ τ).trans_lt ((le_max_right b _).trans_lt hs)
    have hsB : (n : ℝ) + M ≤ (d.exponent + s + (r : ℂ) / 2).re := by
      have hh := (le_max_left b (max σ τ)).trans_lt hs
      simp only [b, Complex.add_re] at hh ⊢
      linarith
    let J (Θ : 𝓢(Mat, ℂ)) (y : G) := ∫ g,
      complexJacquetMatrixIntegrand d (fun g => B f (y * g)) Θ s g ∂μ
    have hc (v : KF[e]) : (T v).val = rightDerivative (matrixModel ℂ n) X v := by
      dsimp only [T]
      rw [complexStandardLie, principalSeriesLie, kFiniteLie_one_tmul_apply_coe]
    have hD := (complexSquareConvolutionDerivative μ d (B f) (hB.2.1 f).continuous C₀ M hC₀ hb Φ s hsB x X).const_mul (L s)
    change HasDerivAt (fun t => L s * J Φ (ComplexGodement.rightExponential x X t))
      (L s * (β s * J Φ x + J Ψ x)) 0 at hD
    have hB' := hasDerivAt_rightDerivative_exponential (hB.2.1 (F s)) x X
    have hD' := hD.congr_of_eventuallyEq (Eventually.of_forall fun t => hσ s hsσ (ComplexGodement.rightExponential x X t))
    change B (T (F s)) x = _
    rw [hB.2.2.2.2 X (F s) (T (F s)) (hc (F s)), hB'.unique hD', hσ s hsσ x, hτ s hsτ x]
    change L s * (β s * J Φ x + J Ψ x) = β s * (L s * J Φ x) + L s * J Ψ x
    ring
  have he : T (F s₀) = β s₀ • F s₀ + V s₀ := by
    apply hInj
    funext x
    simpa only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using congrFun (hEq x) s₀
  rw [he]
  let S := squareConvolutionSpan μ d e B s₀
  exact S.add_mem (S.smul_mem _ (mem_squareConvolutionSpan hΦ hF)) (mem_squareConvolutionSpan hΨ hV)

/-- At every spectral point the normalized standard square Gaussian convolutions span the
irreducible compact-finite standard module whose angular weights are ordered. -/
def ComplexSquareConvolutionSpanStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure] (d : ComplexCharacterData) (e : Fin n → ComplexCharacterData),
    Monotone (fun j => (e j).weight) →
    IsIrreducibleGKModule (complexStandardRep n (List.ofFn e)) (complexStandardLie n (List.ofFn e)) →
    ∀ (a : ℂˣ) (B : KF[e] →ₗ[ℂ] (G → ℂ)), IsComplexWhittakerIntertwiner r (List.ofFn e) a B → B ≠ 0 →
    ∀ s₀ : ℂ, squareConvolutionSpan μ d e B s₀ = ⊤

set_option maxHeartbeats 900000 in
theorem complexSquareConvolutionSpan : ComplexSquareConvolutionSpanStatement (r := r) := by
  intro μ hμ d e hm hirr a B hB hB₀ s₀
  let S := squareConvolutionSpan μ d e B s₀
  let ρ := complexStandardRep n (List.ofFn e)
  let π := complexStandardLie n (List.ofFn e)
  have hInj := hB.injective_of_irreducible hB₀ hirr
  have hK (k : K) : S ≤ S.comap (ρ k) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨Φ, P, f, F, hΦ, hF, rfl⟩
    exact trace_generator_compact μ d e a B hB hInj s₀ k Φ P hΦ f F hF
  have hX (X : Mat) : S ≤ S.comap (π (1 ⊗ₜ[ℝ] X)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨Φ, P, f, F, hΦ, hF, rfl⟩
    exact trace_generator_lie μ d e a B hB hInj s₀ X Φ P hΦ f F hF
  have hLie (X : ℂ ⊗[ℝ] Mat) (v : KF[e]) (hv : v ∈ S) : π X v ∈ S := by
    induction X using TensorProduct.inductionOn with
    | tmul z Y =>
      have he : (z ⊗ₜ[ℝ] Y : ℂ ⊗[ℝ] Mat) = z • (1 ⊗ₜ[ℝ] Y) := by simp [TensorProduct.smul_tmul']
      rw [he, map_smul, LinearMap.smul_apply]
      exact S.smul_mem z (hX Y hv)
    | add X Y hX hY =>
      rw [map_add, LinearMap.add_apply]
      exact S.add_mem hX hY
  have hCases := hirr.2 S (fun k _ hv => hK k hv) hLie
  obtain ⟨Φ, P, f, F, c, hΦ, hF, hc, hI, hV⟩ := complexSquareConvolutionUnit μ d e hm a B hB
  have hmem : F s₀ ∈ S := mem_squareConvolutionSpan hΦ ⟨hF.1, hV⟩
  refine hCases.resolve_left fun he => ?_
  have hz := (Submodule.mem_bot ℂ).mp (he ▸ hmem)
  exact hc ((hI s₀).symm.trans (congrArg (fun v : KF[e] => v.val (1 : G)) hz))

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
