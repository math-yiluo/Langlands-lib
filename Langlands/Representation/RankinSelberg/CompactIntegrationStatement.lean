import Langlands.Representation.RankinSelberg.QuotientIntegrals
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! A finite weighted formula for the compact variable of an equal-rank integral. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker

universe uF uV uW

/-- One finite family of representatives and weights computes every compact
average, and every absolute compact average, of the specified equal-rank data. -/
def EqualRankCompactIntegrationStatement (F : Type uF) [Field F]
    [TopologicalSpace F] [IsTopologicalRing F] (n : ℕ) : Prop :=
  letI := borel (Langlands.GeneralLinear (n + 1) F)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  ∀ (K : Set (Langlands.GeneralLinear (n + 1) F)), IsCompact K →
  ∀ (κ : Measure K) [IsFiniteMeasure κ],
  ∀ (abv : AbsoluteValue F ℝ),
    (∀ k : K, abv (Matrix.det k.val.val) = 1) →
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
  ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
  ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
    IsSmooth π → IsSmooth σ →
  ∀ (ψ : UnitaryAdditiveCharacter F)
    (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ)
    (f : (coefficientModel π ℓ).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)),
  ∃ (m : ℕ) (k : Fin m → K) (c : Fin m → ℝ),
    (∀ i, 0 ≤ c i) ∧ (∑ i, c i) = κ.real Set.univ ∧
    ∀ (g : Langlands.GeneralLinear (n + 1) F) (s : ℂ),
      let H := fun z : K => equalRankFunction ψ abv f.val f'.val Φ s (g * z.val)
      Integrable H κ ∧
      (∫ z, H z ∂κ) = ∑ i, (c i : ℂ) * H (k i) ∧
      (∫⁻ z, ‖H z‖ₑ ∂κ) = ∑ i, ENNReal.ofReal (c i) * ‖H (k i)‖ₑ

end Langlands.RankinSelberg
