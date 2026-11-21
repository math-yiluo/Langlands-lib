import Langlands.Automorphic.AssociatedGammaCuspidalEquation
import Langlands.Global.RankinSelberg.ComplexLocalEqualCharacterReduction
import Langlands.Global.RankinSelberg.ComplexLocalJacquetEndpointConvergence
import Langlands.Global.RankinSelberg.ComplexLocalNormalizedGrowth

/-! # From standard-character normalized growth to the exact equal-rank equation -/

noncomputable section

open MeasureTheory
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open scoped SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal
open Langlands.Global.FunctionalEquationComparison.CompletedEquationAdapter
  (complexPairLFactor_denominator_ne_zero)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

/-- The ordinary equal pair has the entire normalization and strip bounds for the
standard additive character at every rank. -/
def ComplexLocalEqualStandardGrowthStatement : Prop :=
  ∀ (r : ℕ) (ds es : List ComplexCharacterData), ds.length = r + 1 → es.length = r + 1 →
  ∀ (D : ComplexQuotientMeasureData r)
    (W V : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (Φ : 𝓢(Fin (r + 1) → ℂ, ℂ)),
    W ∈ complexWhittakerModel r ds 1 → V ∈ complexWhittakerModel r es (-1) →
    HasComplexPairNormalizedGrowth ds es 1 (complexCentralSign es ^ r)
      (complexEqualIntegral D W V Φ) (complexEqualDualIntegral 1 D W V Φ)

/-- The normalized standard-character induction conclusion implies the published
local equal-rank functional equation with all analytic clauses. -/
def ComplexLocalEqualGrowthReductionStatement : Prop :=
  ComplexLocalEqualStandardGrowthStatement → ComplexLocalEqualFunctionalEquationStatement

private theorem meromorphicOn_divide_denominator (L : ReciprocalEntire) {N : ℂ → ℂ}
    (hN : Differentiable ℂ N) : MeromorphicOn (fun s => N s * (L.denominator s)⁻¹) Set.univ :=
  fun s _ => (hN.analyticAt s).meromorphicAt.mul (L.entire.analyticAt s).meromorphicAt.inv

set_option maxHeartbeats 800000 in
theorem complexLocalEqualGrowthReduction : ComplexLocalEqualGrowthReductionStatement := by
  intro hGrowth
  apply complexLocalEqualCharacterReduction
  intro r ds es hds hes D W V Φ hW hV
  let L := complexPairLFactor ds es
  let Ld := complexPairLFactor (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)
  obtain ⟨σ, hInt⟩ := complexLocalEqualEndpointConvergence hds hes 1 D W V Φ hW hV
  obtain ⟨N, Nd, hN, hNd, _, _, ⟨τ, hT⟩, hEq⟩ := hGrowth r ds es hds hes D W V Φ hW hV
  obtain ⟨ρ, hρ⟩ := complexPairLFactor_denominator_ne_zero ds es
  obtain ⟨ρd, hρd⟩ := complexPairLFactor_denominator_ne_zero
    (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)
  let A := max (max σ τ) (max ρ ρd)
  have hAσ : σ ≤ A := (le_max_left σ τ).trans (le_max_left _ _)
  have hAτ : τ ≤ A := (le_max_right σ τ).trans (le_max_left _ _)
  have hAρ : ρ ≤ A := (le_max_left ρ ρd).trans (le_max_right _ _)
  have hAρd : ρd ≤ A := (le_max_right ρ ρd).trans (le_max_right _ _)
  have hP (s : ℂ) (hs : A < s.re) := (hInt s (hAσ.trans_lt hs)).1
  have hD (s : ℂ) (hs : A < s.re) := (hInt s (hAσ.trans_lt hs)).2
  have hOpen : IsOpen {s : ℂ | A < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hHol := differentiableOn_complexEqualIntegral D W V Φ hOpen hP
  have hHold : DifferentiableOn ℂ (complexEqualDualIntegral 1 D W V Φ) {s : ℂ | A < s.re} := by
    have he : complexEqualDualIntegral 1 D W V Φ =
        complexEqualIntegral D (ArchimedeanLocal.dualFunction (r + 1) W)
          (ArchimedeanLocal.dualFunction (r + 1) V) (complexFourierTransform 1 Φ) := by
      funext s
      rfl
    rw [he]
    exact differentiableOn_complexEqualIntegral D _ _ _ hOpen hD
  refine ⟨A, fun s => N s * (L.denominator s)⁻¹, fun s => Nd s * (Ld.denominator s)⁻¹,
    hP, hD, hHol, hHold, meromorphicOn_divide_denominator L hN,
    meromorphicOn_divide_denominator Ld hNd, ?_, ?_, ?_⟩
  · intro s hs
    change complexEqualIntegral D W V Φ s = N s * (L.denominator s)⁻¹
    rw [(hT s (hAτ.trans_lt hs)).1]
    change _ = (L.denominator s * _) * (L.denominator s)⁻¹
    rw [mul_comm (L.denominator s), mul_assoc, mul_inv_cancel₀ (hρ s (hAρ.trans_lt hs)), mul_one]
  · intro s hs
    change complexEqualDualIntegral 1 D W V Φ s = Nd s * (Ld.denominator s)⁻¹
    rw [(hT s (hAτ.trans_lt hs)).2]
    change _ = (Ld.denominator s * _) * (Ld.denominator s)⁻¹
    rw [mul_comm (Ld.denominator s), mul_assoc, mul_inv_cancel₀ (hρd s (hAρd.trans_lt hs)), mul_one]
  · filter_upwards with s
    rw [hEq s]
    ring

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
