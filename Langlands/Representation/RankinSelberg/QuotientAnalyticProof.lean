import Langlands.Representation.RankinSelberg.QuotientAnalyticStatement
import Langlands.Representation.RankinSelberg.RootAverageAnalyticProof
import Langlands.Representation.RankinSelberg.QuotientRootIntegrationProof
import Langlands.Representation.RankinSelberg.IntegrandContinuityProof

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open RationalContinuationLinear
open scoped BigOperators

universe uF uV uW

/-- Transfer compact-root estimates to the actual quotient integrals. -/
theorem equalRankQuotientAnalytic {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    EqualRankQuotientAnalyticStatement.{uF, uV, uW} F T n := by
  classical
  intro hM hI
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
  let κ := (generalLinearHaar F.Carrier n).restrict (K : Set _)
  let A := Fin (n + 1) → F.Carrierˣ
  let dA : Measure A := Measure.pi (fun _ => localMultiplicativeHaar F.Carrier)
  let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let w : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  intro V _ _ W _ _ π σ ψ hsπ hsσ hπ hσ
  obtain ⟨D, hD, hroot⟩ :=
    equalRankRootAverageAnalytic F T n hM V W π σ ψ hsπ hsσ hπ hσ
  refine ⟨D, hD, ?_⟩
  intro ℓ ℓ' hright μ hμ
  obtain ⟨hconv, hrat, hclear⟩ := hroot ℓ ℓ'
  let H := fun (f : (coefficientModel π ℓ).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)) (s : ℂ) (a : A)
    (z : Langlands.GeneralLinear (n + 1) F.Carrier) =>
    equalRankFunction ψ (normalizedAbsoluteValue T) f.val f'.val Φ s
      (Iwasawa.diagonalUnits (d a) * z) * w a
  let J := fun f f' Φ s => ∫ a, ∫ z, H f f' Φ s a z ∂κ ∂dA
  have hmeas (f : (coefficientModel π ℓ).toSubmodule)
      (f' : (coefficientModel σ ℓ').toSubmodule)
      (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)) (s : ℂ) :
      Measurable (equalRankIntegrand ψ (normalizedAbsoluteValue T) f.val f'.val Φ s) :=
    (equalRankIntegrandContinuous F.Carrier n (normalizedAbsoluteValue T)
      (NNReal.continuous_coe.comp T.continuous_normalizedAbsHom)
      V W π σ hsπ hsσ ψ ℓ ℓ' f f' Φ s).measurable
  have htransport (f : (coefficientModel π ℓ).toSubmodule)
      (f' : (coefficientModel σ ℓ').toSubmodule)
      (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)) (s : ℂ) :
      (EqualRankConverges ψ (normalizedAbsoluteValue T) μ f.val f'.val Φ s ↔
        (∫⁻ a, ∫⁻ z, ‖H f f' Φ s a z‖ₑ ∂κ ∂dA) < ⊤) ∧
      (EqualRankConverges ψ (normalizedAbsoluteValue T) μ f.val f'.val Φ s →
        equalRankModelIntegral ψ (normalizedAbsoluteValue T) μ π σ ℓ ℓ' f f' Φ s =
          J f f' Φ s) :=
    (quotientRootIntegration F T n hI μ hμ).2
      (equalRankIntegrand ψ (normalizedAbsoluteValue T) f.val f'.val Φ s)
      (hmeas f f' Φ s)
  have hdata (f : (coefficientModel π ℓ).toSubmodule)
      (f' : (coefficientModel σ ℓ').toSubmodule)
      (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)) :
      ∃ b : ℝ, ∀ s : ℂ, b < s.re →
        EqualRankConverges ψ (normalizedAbsoluteValue T) μ f.val f'.val Φ s ∧
        equalRankModelIntegral ψ (normalizedAbsoluteValue T) μ π σ ℓ ℓ' f f' Φ s =
          J f f' Φ s := by
    obtain ⟨b, hb⟩ := hconv f f' Φ
    refine ⟨b, fun s hs => ?_⟩
    have hc := (htransport f f' Φ s).1.mpr (hb s hs).2
    exact ⟨hc, (htransport f f' Φ s).2 hc⟩
  refine ⟨?_, ?_, ?_⟩
  · intro f f' Φ
    obtain ⟨b, hb⟩ := hdata f f' Φ
    exact ⟨b, fun s hs => (hb s hs).1⟩
  · intro f f' Φ
    obtain ⟨R, hR⟩ := hrat f f' Φ
    obtain ⟨b, hb⟩ := hdata f f' Φ
    exact ⟨R, continuation_of_eq_on_right hR ⟨b, fun s hs => (hb s hs).2⟩⟩
  · intro R hR
    obtain ⟨f, f', Φ, hR⟩ := hR
    obtain ⟨b, hb⟩ := hdata f f' Φ
    exact hclear f f' Φ R
      (continuation_of_eq_on_right hR ⟨b, fun s hs => (hb s hs).2.symm⟩)

end Langlands.RankinSelberg
