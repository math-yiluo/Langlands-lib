import Langlands.Representation.RankinSelberg.AnalyticStatement

/-! Uniform finite averages for normalized compact integration at zero rows. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker

universe uF uV uW

/-- Uniform finite compact averages of the zero-row unequal-rank integrand,
with the mass-one Haar restriction to the actual integral general linear subgroup.
The ranks differ by the arbitrary positive gap `k + 1`. -/
def UnequalRankZeroRowNormalizedCompactIntegrationStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n k : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
  let κ := (generalLinearHaar F.Carrier n).restrict (K : Set _)
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
  ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
  ∀ (π : Representation ℂ
      (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
    IsSmooth π → IsSmooth σ →
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ℓ : glFunctionals ψ (n + (0 + k + 1)) π)
    (ℓ' : glInverseFunctionals ψ n σ)
    (f : (coefficientModel π ℓ).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule),
  ∃ (m : ℕ) (z : Fin m → K) (c : Fin m → ℝ),
    (∀ i, 0 ≤ c i) ∧ (∑ i, c i) = 1 ∧
    ∀ (g : Langlands.GeneralLinear (n + 1) F.Carrier) (s : ℂ),
      let H := fun u : Langlands.GeneralLinear (n + 1) F.Carrier =>
        unequalRankFunction ψ (normalizedAbsoluteValue T) 0 k f.val f'.val s 0 (g * u)
      Integrable H κ ∧
      (∫ u, H u ∂κ) = ∑ i, (c i : ℂ) * H (z i).val ∧
      (∫⁻ u, ‖H u‖ₑ ∂κ) = ∑ i, ENNReal.ofReal (c i) * ‖H (z i).val‖ₑ

end Langlands.RankinSelberg
