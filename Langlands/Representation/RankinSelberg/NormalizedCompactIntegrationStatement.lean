import Langlands.Representation.RankinSelberg.AnalyticStatement

/-! Finite averages for the actual normalized compact Haar variable. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker

universe uF uV uW

/-- Uniform finite compact averages with the actual mass-one Haar restriction
to the integral general linear subgroup of the supplied local field. -/
def EqualRankNormalizedCompactIntegrationStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
  let κ := (generalLinearHaar F.Carrier n).restrict (K : Set _)
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
  ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
  ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
    IsSmooth π → IsSmooth σ →
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ)
    (f : (coefficientModel π ℓ).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)),
  ∃ (m : ℕ) (k : Fin m → K) (c : Fin m → ℝ),
    (∀ i, 0 ≤ c i) ∧ (∑ i, c i) = 1 ∧
    ∀ (g : Langlands.GeneralLinear (n + 1) F.Carrier) (s : ℂ),
      let H := fun z : Langlands.GeneralLinear (n + 1) F.Carrier =>
        equalRankFunction ψ (normalizedAbsoluteValue T) f.val f'.val Φ s (g * z)
      Integrable H κ ∧
      (∫ z, H z ∂κ) = ∑ i, (c i : ℂ) * H (k i).val ∧
      (∫⁻ z, ‖H z‖ₑ ∂κ) = ∑ i, ENNReal.ofReal (c i) * ‖H (k i).val‖ₑ

end Langlands.RankinSelberg
