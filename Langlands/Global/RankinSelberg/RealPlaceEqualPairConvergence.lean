import Langlands.Global.RankinSelberg.RealUniformLocalTheoryReduction
import Langlands.Global.RankinSelberg.RealEqualDualConvergence

/-! # Convergence for actual real equal-rank place restrictions -/

noncomputable section

open MeasureTheory NumberField
open Langlands.Automorphic Langlands.LocalFactor.Archimedean
open Langlands.Global.HeckeFunctionalEquation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal

attribute [local instance] archimedeanEquationRealGLMeasurable
  archimedeanEquationRealGLBorel archimedeanEquationRealNMeasurable
  archimedeanEquationRealNBorel archimedeanEquationRealQMeasurable
  archimedeanEquationRealQBorel

/-- The ordinary and dual equal-rank integrals of actual real-place restrictions converge
absolutely and are holomorphic on a common right half-plane. -/
theorem realPlaceEqualPairConvergence
    {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    {r : ℕ} (T T' : CuspidalOperatorRealization F r)
    (v : {v : InfinitePlace F // v.IsReal}) (a : ℝˣ)
    (ha : IsRealAdditiveComponent ψ v.1 v.2 a)
    {d d' : List RealBlock}
    (hd : T.realization.HasRealPlaceParameter v d)
    (hd' : T'.realization.HasRealPlaceParameter v d')
    (D : RealQuotientMeasureData r) (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ)
    {W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hW : IsRealPlaceWhittaker F T ψ.complex v W)
    (hW' : IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W') :
    ∃ σ : ℝ, (∀ s : ℂ, σ < s.re → Integrable (realEqualIntegrand W W' Φ s) D.measure) ∧
      (∀ s : ℂ, σ < s.re → Integrable
        (realEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
          (ArchimedeanLocal.dualFunction (r + 1) W') (realFourierTransform a Φ) s)
        D.measure) ∧
      DifferentiableOn ℂ (realEqualIntegral D W W' Φ) {s : ℂ | σ < s.re} ∧
      DifferentiableOn ℂ (realEqualDualIntegral a D W W' Φ) {s : ℂ | σ < s.re} := by
  obtain ⟨hreg, hgrowth⟩ := realUniformWhittakerRegularity r d a W
    ((realPlaceUniformWhittakerModel F ψ hψ r T v a ha d hd W).1 hW)
  obtain ⟨hreg', hgrowth'⟩ := realUniformWhittakerRegularity r d' (-a) W'
    ((realPlaceUniformWhittakerModel F ψ hψ r T' v a ha d' hd' W').2 hW')
  exact realEqualPairConvergence r D a a W W' Φ hreg hgrowth hreg' hgrowth'

end Langlands.Global.RankinSelbergGlobal
