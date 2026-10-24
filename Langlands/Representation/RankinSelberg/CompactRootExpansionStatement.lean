import Langlands.Representation.RankinSelberg.NormalizedCompactIntegrationStatement
import Langlands.Representation.RankinSelberg.RootModelExpansionStatement

/-! A finite-function formula for the normalized compact root-coordinate average. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker
open scoped BigOperators

universe uF uV uW

/-- Fixed finite functions, followed by test-dependent Schwartz coefficients,
compute the actual compact average and absolute average of the root integrand. -/
def EqualRankCompactRootExpansionStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
  let κ := (generalLinearHaar F.Carrier n).restrict (K : Set _)
  let A := Fin (n + 1) → F.Carrierˣ
  let toDiagonal : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let weight : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  let spectral : A → ℂ → ℂ := fun a s =>
    ∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^ ((i.val + 1 : ℂ) * s)
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
  ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
  ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (ψ : UnitaryAdditiveCharacter F.Carrier),
    IsSmooth π → IsSmooth σ →
    CoefficientTorusExpansion (standardCharacter ψ n) π →
    CoefficientTorusExpansion (inverseStandardCharacter ψ n) σ →
  ∃ (m : ℕ) (η : Fin m → A → ℂ),
    (∀ j, Continuous (η j) ∧
      FiniteDimensional ℂ (Submodule.span ℂ
        (Set.range fun b : A => fun a : A => η j (b * a)))) ∧
    ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ)
      (f : (coefficientModel π ℓ).toSubmodule)
      (f' : (coefficientModel σ ℓ').toSubmodule)
      (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)),
    ∃ (r : ℕ) (c : Fin r → ℝ)
      (Ψ : Fin r → Fin m → SchwartzBruhat (Fin (n + 1) → F.Carrier)),
      (∀ t, 0 ≤ c t) ∧ (∑ t, c t) = 1 ∧
      ∀ (a : A) (s : ℂ),
        let H := fun z : Langlands.GeneralLinear (n + 1) F.Carrier =>
          equalRankFunction ψ (normalizedAbsoluteValue T) f.val f'.val Φ s
            (GeneralLinear.Iwasawa.diagonalUnits (toDiagonal a) * z) * weight a
        let S := fun t : Fin r =>
          ∑ j, Ψ t j (fun i => (a i : F.Carrier)) * η j a * spectral a s
        Integrable H κ ∧
        (∫ z, H z ∂κ) = ∑ t, (c t : ℂ) * S t ∧
        (∫⁻ z, ‖H z‖ₑ ∂κ) = ∑ t, ENNReal.ofReal (c t) * ‖S t‖ₑ

end Langlands.RankinSelberg
