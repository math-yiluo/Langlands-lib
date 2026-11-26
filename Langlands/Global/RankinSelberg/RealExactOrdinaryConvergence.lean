import Langlands.Global.RankinSelberg.ArchimedeanOrdinaryNormalizedTests
import Langlands.Global.RankinSelberg.RealEqualDualConvergence
import Langlands.Global.RankinSelberg.RealUnequalPairConvergence
import Langlands.Global.RankinSelberg.RealWhittakerEvaluation

/-! # Half-plane convergence for exact real ordinary tests -/

noncomputable section

open MeasureTheory

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.LocalFactor.Archimedean ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)

private local instance (r : ℕ) : MeasurableSpace (Langlands.GeneralLinear (r + 1) ℝ) := borel _
private local instance (r : ℕ) : BorelSpace (Langlands.GeneralLinear (r + 1) ℝ) := ⟨rfl⟩
private local instance (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ) := borel _
private local instance (r : ℕ) : BorelSpace (Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ) := ⟨rfl⟩
private local instance (r : ℕ) : MeasurableSpace (LeftUnipotentQuotient r ℝ) := borel _
private local instance (r : ℕ) : BorelSpace (LeftUnipotentQuotient r ℝ) := ⟨rfl⟩

/-- In both rank regimes the ordinary and dual kernels of the exact real Whittaker
tests are integrable, and the integrals are holomorphic, on a common right half-plane. -/
def RealExactOrdinaryConvergenceStatement : Prop :=
  (∀ (r t : ℕ) (h : t < r) (ds es : List RealBlock) (a : ℝˣ) (D : RealQuotientMeasureData t)
      (i : realWhittakerModel r ds a × realWhittakerModel t es (-a)),
      ∃ σ : ℝ,
        (∀ s : ℂ, σ < s.re → Integrable (realUnequalIntegrand h i.1 i.2 s) D.measure) ∧
        (∀ s : ℂ, σ < s.re → Integrable (realUnequalDualKernel h i.1 i.2 s)
          (realUnequalDualMeasure (r := r) a D)) ∧
        DifferentiableOn ℂ (realOrdinaryUnequalTest h ds es a D i) {s | σ < s.re} ∧
        DifferentiableOn ℂ (realUnequalDualIntegral h a D i.1 i.2) {s | σ < s.re}) ∧
  ∀ (r : ℕ) (ds es : List RealBlock) (a : ℝˣ) (D : RealQuotientMeasureData r)
    (i : realWhittakerModel r ds a × realWhittakerModel r es (-a) ×
      SchwartzMap (Fin (r + 1) → ℝ) ℂ),
    ∃ σ : ℝ,
      (∀ s : ℂ, σ < s.re → Integrable (realEqualIntegrand i.1 i.2.1 i.2.2 s) D.measure) ∧
      (∀ s : ℂ, σ < s.re → Integrable (realEqualIntegrand
        (ArchimedeanLocal.dualFunction (r + 1) i.1) (ArchimedeanLocal.dualFunction (r + 1) i.2.1)
        (realFourierTransform (-a) i.2.2) s) D.measure) ∧
      DifferentiableOn ℂ (realOrdinaryEqualTest r ds es a D i) {s | σ < s.re} ∧
      DifferentiableOn ℂ (realEqualDualIntegral (-a) D i.1 i.2.1 i.2.2) {s | σ < s.re}

theorem realExactOrdinaryConvergence : RealExactOrdinaryConvergenceStatement := by
  constructor
  · intro r t h ds es a D i
    exact realUnequalPairConvergence r t h D a i.1 i.2
      (realLocalWhittakerRegularity r ds a i.1 i.1.property)
      (realExactWhittakerDerivativeGrowth r ds a i.1.property).2
      (realLocalWhittakerRegularity t es (-a) i.2 i.2.property)
      (realExactWhittakerDerivativeGrowth t es (-a) i.2.property).2
  · intro r ds es a D i
    exact realEqualPairConvergence r D a (-a) i.1 i.2.1 i.2.2
      (realLocalWhittakerRegularity r ds a i.1 i.1.property)
      (realExactWhittakerDerivativeGrowth r ds a i.1.property).2
      (realLocalWhittakerRegularity r es (-a) i.2.1 i.2.1.property)
      (realExactWhittakerDerivativeGrowth r es (-a) i.2.1.property).2

end Langlands.Global.RankinSelbergGlobal
