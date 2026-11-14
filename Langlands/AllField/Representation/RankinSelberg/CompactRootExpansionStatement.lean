import Langlands.Representation.RankinSelberg.CompactRootExpansionStatement
import Langlands.AllField.Representation.RankinSelberg.NormalizedCompactIntegrationStatement
import Langlands.AllField.Representation.RankinSelberg.RootModelExpansionStatement
/-! A finite-function formula for the normalized compact root-coordinate average. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankNormalizedCompactIntegrationStatement EqualRankRootExpansionStatement QuotientHaarExistenceStatement RootTorusProductStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open scoped BigOperators

universe uF uV uW

/-- Fixed finite functions, followed by test-dependent Schwartz coefficients,
compute the actual compact average and absolute average of the root integrand. -/
def EqualRankCompactRootExpansionStatement 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel (Langlands.GeneralLinear (n + 1) F)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F).integer n
  let κ := (generalLinearHaar F n).restrict (K : Set _)
  let A := Fin (n + 1) → Fˣ
  let toDiagonal : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let weight : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  let spectral : A → ℂ → ℂ := fun a s =>
    ∏ i, (T.normalizedAbs (a i : F) : ℂ) ^ ((i.val + 1 : ℂ) * s)
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
  ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
  ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ψ : UnitaryAdditiveCharacter F),
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
      (Φ : SchwartzBruhat (Fin (n + 1) → F)),
    ∃ (r : ℕ) (c : Fin r → ℝ)
      (Ψ : Fin r → Fin m → SchwartzBruhat (Fin (n + 1) → F)),
      (∀ t, 0 ≤ c t) ∧ (∑ t, c t) = 1 ∧
      ∀ (a : A) (s : ℂ),
        let H := fun z : Langlands.GeneralLinear (n + 1) F =>
          equalRankFunction ψ (normalizedAbsoluteValue T) f.val f'.val Φ s
            (GeneralLinear.Iwasawa.diagonalUnits (toDiagonal a) * z) * weight a
        let S := fun t : Fin r =>
          ∑ j, Ψ t j (fun i => (a i : F)) * η j a * spectral a s
        Integrable H κ ∧
        (∫ z, H z ∂κ) = ∑ t, (c t : ℂ) * S t ∧
        (∫⁻ z, ‖H z‖ₑ ∂κ) = ∑ t, ENNReal.ofReal (c t) * ‖S t‖ₑ

end Langlands.AllField.RankinSelberg
