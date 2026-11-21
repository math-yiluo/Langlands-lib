import Langlands.Global.RankinSelberg.ComplexLocalEqualSimpleRootBound
import Langlands.Global.RankinSelberg.ComplexLocalEqualHolomorphy
import Langlands.Global.RankinSelberg.ComplexLocalDualWhittaker
import Langlands.Global.RankinSelberg.ComplexLocalFourierSchwartz
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerGauge
import Langlands.Global.RankinSelberg.ComplexPlaceWhittakerAnalyticProof

/-! # Convergence of the two complex equal-rank local integrals -/

noncomputable section

open MeasureTheory NumberField
open Langlands.Archimedean Langlands.Automorphic Langlands.LocalFactor.Archimedean
open Langlands.Global.HeckeFunctionalEquation
open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal ComplexLocalConvergence

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

private theorem sum_abs_eq_logSums {r : ℕ} (x : Fin (r + 1) → ℝ) :
    ∑ j, |x j| = positiveLogSum x + positiveLogSum (-x) := by
  rw [positiveLogSum, positiveLogSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  change |x j| = max (x j) 0 + max (-x j) 0
  rcases le_or_gt 0 (x j) with hj | hj
  · simp [abs_of_nonneg hj, max_eq_left hj, max_eq_right (neg_nonpos.mpr hj)]
  · simp [abs_of_neg hj, max_eq_right hj.le, max_eq_left (neg_nonneg.mpr hj.le)]

private theorem hasSimpleRootLogBound_of_complexWhittakerModel {r : ℕ}
    {d : List ComplexCharacterData} {a : ℂˣ} {W : Langlands.GeneralLinear (r + 1) ℂ → ℂ}
    (hW : W ∈ complexWhittakerModel r d a) : HasSimpleRootLogBound W := by
  obtain ⟨N, hN⟩ := complexWhittakerSimpleRootMajorization r d a ⟨W, hW⟩
  refine ⟨N, Nat.cast_nonneg N, fun L _ => ?_⟩
  obtain ⟨M, hM⟩ := exists_nat_ge L
  obtain ⟨C, hC, hbound⟩ := hN M []
  refine ⟨C, hC, fun x k => ?_⟩
  have htorus : ComplexLocalWhittakerGauge.logTorus x = expDiagonal x := by
    apply Units.ext
    rw [ComplexLocalWhittakerGauge.logTorus_val, expDiagonal_val]
  have hroot : 0 ≤ simpleRootLogSum x :=
    Finset.sum_nonneg fun _ _ => le_max_right _ _
  have hx := hbound x k
  simp only [List.map_nil, List.prod_nil, Module.End.one_apply, htorus,
    sum_abs_eq_logSums] at hx
  exact hx.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (sub_le_sub_left (mul_le_mul_of_nonneg_right hM hroot) _)) hC)

private theorem exists_complexEqualConvergence {r : ℕ}
    {d d' : List ComplexCharacterData} {a : ℂˣ} {W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ}
    (D : ComplexQuotientMeasureData r) (Φ : SchwartzMap (Fin (r + 1) → ℂ) ℂ)
    (hW : W ∈ complexWhittakerModel r d a) (hW' : W' ∈ complexWhittakerModel r d' (-a)) :
    ∃ σ : ℝ, (∀ s : ℂ, σ < s.re → Integrable (complexEqualIntegrand W W' Φ s) D.measure) ∧
      DifferentiableOn ℂ (complexEqualIntegral D W W' Φ) {s : ℂ | σ < s.re} := by
  have hrow : Continuous (Langlands.RankinSelberg.lastRow :
      Langlands.GeneralLinear (r + 1) ℂ → _) :=
    continuous_pi fun j => (GeneralLinear.entry (R := ℂ) (Fin.last r) j).continuous
  have hkernel := ((contMDiff_of_mem_complexWhittakerModel hW).continuous.mul
    (contMDiff_of_mem_complexWhittakerModel hW').continuous).mul (Φ.continuous.comp hrow)
  obtain ⟨σ, hInt⟩ := exists_integrable_complexEqualIntegrand_of_logarithmicKernelBound D
    (ComplexCharacterChange.model_pair_invariant hW hW') hkernel
    (hasLogarithmicKernelBound_of_simpleRoots
      (hasSimpleRootLogBound_of_complexWhittakerModel hW)
      (hasSimpleRootLogBound_of_complexWhittakerModel hW') Φ)
  exact ⟨σ, hInt, differentiableOn_complexEqualIntegral D W W' Φ
    (isOpen_lt continuous_const Complex.continuous_re) hInt⟩

/-- Opposite-character members of complex standard Whittaker models give absolute
convergence and holomorphy of both integrals on a common right half-plane. -/
theorem complexEqualPairConvergence {r : ℕ} {d d' : List ComplexCharacterData}
    (hd : d.length = r + 1) (hd' : d'.length = r + 1)
    (D : ComplexQuotientMeasureData r) {a : ℂˣ} {W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ}
    (Φ : SchwartzMap (Fin (r + 1) → ℂ) ℂ)
    (hW : W ∈ complexWhittakerModel r d a) (hW' : W' ∈ complexWhittakerModel r d' (-a)) :
    ∃ σ : ℝ, (∀ s : ℂ, σ < s.re → Integrable (complexEqualIntegrand W W' Φ s) D.measure) ∧
      (∀ s : ℂ, σ < s.re → Integrable
        (complexEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
          (ArchimedeanLocal.dualFunction (r + 1) W') (complexFourierTransform a Φ) s)
        D.measure) ∧
      DifferentiableOn ℂ (complexEqualIntegral D W W' Φ) {s : ℂ | σ < s.re} ∧
      DifferentiableOn ℂ (complexEqualDualIntegral a D W W' Φ) {s : ℂ | σ < s.re} := by
  obtain ⟨σ, hInt, hHol⟩ := exists_complexEqualConvergence D Φ hW hW'
  obtain ⟨Ψ, hΨ⟩ := exists_schwartz_complexFourierTransform a Φ
  obtain ⟨τ, hIntd, hHold⟩ := exists_complexEqualConvergence D Ψ
    (complexLocalDualWhittaker_mem hd hW) (complexLocalDualWhittaker_mem hd' hW')
  have hσ {s : ℂ} (hs : max σ τ < s.re) : σ < s.re := (le_max_left σ τ).trans_lt hs
  have hτ {s : ℂ} (hs : max σ τ < s.re) : τ < s.re := (le_max_right σ τ).trans_lt hs
  refine ⟨max σ τ, fun s hs => hInt s (hσ hs), ?_, hHol.mono (fun _ => hσ), ?_⟩
  · intro s hs
    rw [← hΨ]
    exact hIntd s (hτ hs)
  · unfold complexEqualDualIntegral
    rw [← hΨ]
    exact hHold.mono (fun _ => hτ)

/-- The convergence result for actual complex-place restrictions of cuspidal Whittaker
coefficients. -/
theorem complexPlaceEqualPairConvergence
    {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    {r : ℕ} (T T' : CuspidalOperatorRealization F r)
    (w : {w : InfinitePlace F // w.IsComplex}) (a : ℂˣ)
    (ha : IsComplexAdditiveComponent ψ w.1 w.2 a)
    {d d' : List ComplexCharacterData}
    (hd : T.realization.HasComplexPlaceParameter w d)
    (hd' : T'.realization.HasComplexPlaceParameter w d')
    (D : ComplexQuotientMeasureData r) (Φ : SchwartzMap (Fin (r + 1) → ℂ) ℂ)
    {W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ}
    (hW : IsComplexPlaceWhittaker F T ψ.complex w W)
    (hW' : IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w W') :
    ∃ σ : ℝ, (∀ s : ℂ, σ < s.re → Integrable (complexEqualIntegrand W W' Φ s) D.measure) ∧
      (∀ s : ℂ, σ < s.re → Integrable
        (complexEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
          (ArchimedeanLocal.dualFunction (r + 1) W') (complexFourierTransform a Φ) s)
        D.measure) ∧
      DifferentiableOn ℂ (complexEqualIntegral D W W' Φ) {s : ℂ | σ < s.re} ∧
      DifferentiableOn ℂ (complexEqualDualIntegral a D W W' Φ) {s : ℂ | σ < s.re} := by
  have hmodel := complexPlaceWhittakerModelReduction
    (complexPlaceWhittakerIntertwinerReduction complexPlaceWhittakerAnalytic)
  exact complexEqualPairConvergence hd.1 hd'.1 D Φ
    ((hmodel F ψ hψ r T w a ha d hd W).1 hW)
    ((hmodel F ψ hψ r T' w a ha d' hd' W').2 hW')

end Langlands.Global.RankinSelbergGlobal
