import Langlands.Representation.RankinSelberg.CompactRootExpansionStatement
import Langlands.Representation.RankinSelberg.FiniteFunctionMellinStatement

/-! Analytic consequences for the actual iterated compact root average. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker
open scoped BigOperators

universe uF uV uW

/-- Conditional torus convergence, rationality, and a fixed Laurent denominator
for the compact root average, uniform over coefficient functionals and tests. -/
def EqualRankRootAverageAnalyticStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) : Prop :=
  FiniteFunctionMellinStatement.{uF} →
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel F.Carrierˣ
  letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
  let κ := (generalLinearHaar F.Carrier n).restrict (K : Set _)
  let A := Fin (n + 1) → F.Carrierˣ
  let dA : Measure A := Measure.pi (fun _ => localMultiplicativeHaar F.Carrier)
  let toDiagonal : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let weight : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
  ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
  ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (ψ : UnitaryAdditiveCharacter F.Carrier),
    IsSmooth π → IsSmooth σ →
    CoefficientTorusExpansion (standardCharacter ψ n) π →
    CoefficientTorusExpansion (inverseStandardCharacter ψ n) σ →
  ∃ d : LaurentCoefficients, d ≠ 0 ∧
    ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ),
      let H := fun (f : (coefficientModel π ℓ).toSubmodule)
          (f' : (coefficientModel σ ℓ').toSubmodule)
          (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)) (s : ℂ) (a : A)
          (z : Langlands.GeneralLinear (n + 1) F.Carrier) =>
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

end Langlands.RankinSelberg
