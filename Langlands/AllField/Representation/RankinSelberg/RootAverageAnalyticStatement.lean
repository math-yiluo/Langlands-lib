import Langlands.Representation.RankinSelberg.RootAverageAnalyticStatement
import Langlands.AllField.Representation.RankinSelberg.CompactRootExpansionStatement
import Langlands.AllField.Representation.RankinSelberg.FiniteFunctionMellinStatement
/-! Analytic consequences for the actual iterated compact root average. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankNormalizedCompactIntegrationStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement FiniteFunctionMellinStatement QuotientHaarExistenceStatement RootTorusProductStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open scoped BigOperators

universe uF uV uW

/-- Conditional torus convergence, rationality, and a fixed Laurent denominator
for the compact root average, uniform over coefficient functionals and tests. -/
def EqualRankRootAverageAnalyticStatement 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) : Prop :=
  FiniteFunctionMellinStatement.{uF} →
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel Fˣ
  letI : BorelSpace Fˣ := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F).integer n
  let κ := (generalLinearHaar F n).restrict (K : Set _)
  let A := Fin (n + 1) → Fˣ
  let dA : Measure A := Measure.pi (fun _ => localMultiplicativeHaar F)
  let toDiagonal : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let weight : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
  ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
  ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ψ : UnitaryAdditiveCharacter F),
    IsSmooth π → IsSmooth σ →
    CoefficientTorusExpansion (standardCharacter ψ n) π →
    CoefficientTorusExpansion (inverseStandardCharacter ψ n) σ →
  ∃ d : LaurentCoefficients, d ≠ 0 ∧
    ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ),
      let H := fun (f : (coefficientModel π ℓ).toSubmodule)
          (f' : (coefficientModel σ ℓ').toSubmodule)
          (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ) (a : A)
          (z : Langlands.GeneralLinear (n + 1) F) =>
        equalRankFunction ψ (normalizedAbsoluteValue T) f.val f'.val Φ s
          (GeneralLinear.Iwasawa.diagonalUnits (toDiagonal a) * z) * weight a
      let average := fun f f' Φ s a => ∫ z, H f f' Φ s a z ∂κ
      let integral := fun f f' Φ s => ∫ a, average f f' Φ s a ∂dA
      (∀ f f' Φ, ∃ b : ℝ, ∀ s : ℂ, b < s.re →
        Integrable (average f f' Φ s) dA ∧
        (∫⁻ a, ∫⁻ z, ‖H f f' Φ s a z‖ₑ ∂κ ∂dA) < ⊤) ∧
      (∀ f f' Φ, ∃ R : RationalFunctions,
        HasRationalContinuation T.residueCardinality (integral f f' Φ) R) ∧
      (∀ f f' Φ (R : RationalFunctions),
        HasRationalContinuation T.residueCardinality (integral f f' Φ) R →
        ∃ P : LaurentCoefficients, laurentToRatFunc P = laurentToRatFunc d * R)

end Langlands.AllField.RankinSelberg
