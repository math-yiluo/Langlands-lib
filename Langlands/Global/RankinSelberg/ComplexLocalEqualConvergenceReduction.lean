import Langlands.Global.RankinSelberg.ComplexLocalWhittakerUniformGrowth
import Langlands.Global.RankinSelberg.ComplexLocalEqualHolomorphy
import Langlands.Global.RankinSelberg.ComplexLocalEqualDualityReduction

/-! # Absolute convergence of the complex equal-rank integrals from simple-root bounds -/

noncomputable section

open MeasureTheory Langlands.LocalFactor.Archimedean
open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal
open ComplexLocalConvergence
open ComplexCharacterChange (model_pair_invariant)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

/-- The logarithmic simple-root bound for every coefficient of the Library's complex
Whittaker model. -/
def ComplexLocalWhittakerSimpleRootBoundStatement : Prop :=
  ∀ (r : ℕ) (d : List ComplexCharacterData), d.length = r + 1 →
    ∀ (a : ℂˣ) (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ),
      W ∈ complexWhittakerModel r d a → HasSimpleRootLogBound W

/-- For each inducing vector, the growth exponent is uniform over the conjugated
simple-root derivative words used in Jacquet's estimate. -/
def ComplexLocalWhittakerUniformGrowthStatement : Prop :=
  ∀ (r : ℕ) (d : List ComplexCharacterData), d.length = r + 1 →
    ∀ (a : ℂˣ) (B : Automorphic.complexStandardKFinite (r + 1) d →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℂ → ℂ)),
      IsComplexWhittakerIntertwiner r d a B →
        ∀ f : Automorphic.complexStandardKFinite (r + 1) d,
          HasUniformSimpleRootDerivativeGrowth a B f

theorem complexLocalWhittakerSimpleRootBound_of_uniformGrowth
    (h : ComplexLocalWhittakerUniformGrowthStatement) :
    ComplexLocalWhittakerSimpleRootBoundStatement := by
  intro r d hd a W hW
  exact hasSimpleRootLogBound_of_uniformDerivativeGrowth hW (h r d hd a)

/-- The original integral admits a meromorphic continuation agreeing with it on a
right half-plane once the integral converges there. -/
def ComplexLocalEqualPrimalContinuationStatement : Prop :=
  ∀ (r : ℕ) (d d' : List ComplexCharacterData), d.length = r + 1 → d'.length = r + 1 →
    ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData r) (W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
      (Φ : SchwartzMap (Fin (r + 1) → ℂ) ℂ),
      W ∈ complexWhittakerModel r d a → W' ∈ complexWhittakerModel r d' (-a) →
      ∀ σ : ℝ, (∀ s : ℂ, σ < s.re → Integrable (complexEqualIntegrand W W' Φ s) D.measure) →
        ∃ (τ : ℝ) (M : ℂ → ℂ), σ ≤ τ ∧ MeromorphicOn M Set.univ ∧
          (∀ s : ℂ, τ < s.re → complexEqualIntegral D W W' Φ s = M s)

/-- Uniform derivative growth and the two meromorphic premises suffice for the
complex equal-rank local functional equation. -/
def ComplexLocalEqualConvergenceReductionStatement : Prop :=
  ComplexLocalWhittakerUniformGrowthStatement →
    ComplexLocalEqualPrimalContinuationStatement →
      ComplexLocalEqualMeromorphicEquationStatement →
        ComplexLocalEqualFunctionalEquationStatement

private theorem continuous_of_complexWhittakerModel {r : ℕ}
    {d : List ComplexCharacterData} {a : ℂˣ} {W : Langlands.GeneralLinear (r + 1) ℂ → ℂ}
    (hW : W ∈ complexWhittakerModel r d a) : Continuous W := by
  let G := Langlands.GeneralLinear (r + 1) ℂ
  let S : Submodule ℂ (G → ℂ) :=
    { carrier := {f | Continuous f}
      zero_mem' := continuous_const
      add_mem' := fun hf hg => Continuous.add hf hg
      smul_mem' := fun c _ hf => Continuous.const_smul hf c }
  have hS : complexWhittakerModel r d a ≤ S := by
    refine iSup₂_le fun B hB => ?_
    rintro _ ⟨f, rfl⟩
    exact (hB.2.1 f).continuous
  exact hS hW

private theorem complexEqualConverges_of_simpleRoots {r : ℕ}
    {d d' : List ComplexCharacterData} {a : ℂˣ} {W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ}
    (hW : W ∈ complexWhittakerModel r d a) (hW' : W' ∈ complexWhittakerModel r d' (-a))
    (hV : HasSimpleRootLogBound W) (hV' : HasSimpleRootLogBound W')
    (D : ComplexQuotientMeasureData r) (Φ : SchwartzMap (Fin (r + 1) → ℂ) ℂ) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Integrable (complexEqualIntegrand W W' Φ s) D.measure := by
  have hrow : Continuous (Langlands.RankinSelberg.lastRow :
      Langlands.GeneralLinear (r + 1) ℂ → _) :=
    continuous_pi fun j => (GeneralLinear.entry (R := ℂ) (Fin.last r) j).continuous
  exact exists_integrable_complexEqualIntegrand_of_logarithmicKernelBound D
    (model_pair_invariant hW hW')
    (((continuous_of_complexWhittakerModel hW).mul (continuous_of_complexWhittakerModel hW')).mul
      (Φ.continuous.comp hrow))
    (hasLogarithmicKernelBound_of_simpleRoots hV hV' Φ)

theorem complexLocalEqualConvergenceReduction : ComplexLocalEqualConvergenceReductionStatement := by
  intro hgrowth hcont heq
  have hbound := complexLocalWhittakerSimpleRootBound_of_uniformGrowth hgrowth
  apply complexLocalEqualDualityReduction ?_ heq
  intro r d d' hd hd' a D W W' Φ hW hW'
  obtain ⟨σ, hInt⟩ := complexEqualConverges_of_simpleRoots hW hW'
    (hbound r d hd a W hW) (hbound r d' hd' (-a) W' hW') D Φ
  obtain ⟨τ, M, hστ, hM, hagree⟩ := hcont r d d' hd hd' a D W W' Φ hW hW' σ hInt
  have hInt' (s : ℂ) (hs : τ < s.re) := hInt s (hστ.trans_lt hs)
  refine ⟨τ, M, hInt', ?_, hM, hagree⟩
  exact differentiableOn_complexEqualIntegral D W W' Φ
    (isOpen_lt continuous_const Complex.continuous_re) hInt'

end Langlands.Global.RankinSelbergGlobal
