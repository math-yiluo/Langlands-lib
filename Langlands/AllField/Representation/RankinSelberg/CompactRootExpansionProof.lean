import Langlands.Representation.RankinSelberg.CompactRootExpansionProof
import Langlands.AllField.Representation.RankinSelberg.CompactRootExpansionStatement
import Langlands.AllField.Representation.RankinSelberg.NormalizedCompactIntegrationProof
import Langlands.AllField.Representation.RankinSelberg.RootModelExpansionProof
import Langlands.AllField.Representation.RankinSelberg.RootSpectralWeightProof
noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankNormalizedCompactIntegrationStatement EqualRankRootExpansionStatement QuotientHaarExistenceStatement RootTorusProductStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement equalRankCompactRootExpansion equalRankNormalizedCompactIntegration equalRankRootExpansion normalizedAbsoluteValue normalizedAbsoluteValue_apply rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open scoped BigOperators

universe uF uV uW

/-- Finite-function formulas for the actual compact root-coordinate averages. -/
theorem equalRankCompactRootExpansion 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) :
    EqualRankCompactRootExpansionStatement.{uF, uV, uW} F T n := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F).integer n
  let κ := (generalLinearHaar F n).restrict (K : Set _)
  let A := Fin (n + 1) → Fˣ
  let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let w : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  let v : A → ℂ → ℂ := fun a s =>
    ∏ i, (T.normalizedAbs (a i : F) : ℂ) ^ ((i.val + 1 : ℂ) * s)
  intro V _ _ W _ _ π σ ψ hsπ hsσ hπ hσ
  obtain ⟨m, η, hη, hexp⟩ := equalRankRootExpansion F T n V W π σ ψ hπ hσ
  refine ⟨m, η, hη, ?_⟩
  intro ℓ ℓ' f f' Φ
  obtain ⟨r, k, c, hc, hmass, havg⟩ :=
    equalRankNormalizedCompactIntegration F T n V W π σ hsπ hsσ ψ ℓ ℓ' f f' Φ
  choose Ψ hΨ using fun t : Fin r => hexp ℓ ℓ' f f' Φ (k t).val
  refine ⟨r, c, Ψ, hc, hmass, ?_⟩
  intro a s
  let H₀ := fun z : Langlands.GeneralLinear (n + 1) F =>
    equalRankFunction ψ (normalizedAbsoluteValue T) f.val f'.val Φ s
      (GeneralLinear.Iwasawa.diagonalUnits (d a) * z)
  let S := fun t : Fin r =>
    ∑ j, Ψ t j (fun i => (a i : F)) * η j a * v a s
  have hpoint (t : Fin r) : H₀ (k t).val * w a = S t := by
    have hdet := ((rootSpectralWeight F T n).2 a (k t).val
      ((rootSpectralWeight F T n).1 (k t)) s).1
    change (f.val.val _ * f'.val.val _ * Φ (lastRow _) *
      determinantWeight (normalizedAbsoluteValue T) _ s) * w a = S t
    rw [hdet]
    change (f.val.val _ * f'.val.val _ * Φ (lastRow _) * v a s) * w a = S t
    calc
      _ = (f.val.val _ * f'.val.val _ * Φ (lastRow _) * w a) * v a s := by ring
      _ = (∑ j, Ψ t j (fun i => (a i : F)) * η j a) * v a s := by
        rw [hΨ t a]
      _ = S t := Finset.sum_mul _ _ _
  obtain ⟨hi, hsum, habs⟩ := havg (GeneralLinear.Iwasawa.diagonalUnits (d a)) s
  change Integrable (fun z => H₀ z * w a) κ ∧
    (∫ z, H₀ z * w a ∂κ) = ∑ t, (c t : ℂ) * S t ∧
    (∫⁻ z, ‖H₀ z * w a‖ₑ ∂κ) = ∑ t, ENNReal.ofReal (c t) * ‖S t‖ₑ
  refine ⟨hi.mul_const (w a), ?_, ?_⟩
  · rw [integral_mul_const, hsum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    rw [mul_assoc, hpoint]
  · calc
      (∫⁻ z, ‖H₀ z * w a‖ₑ ∂κ) = (∫⁻ z, ‖H₀ z‖ₑ ∂κ) * ‖w a‖ₑ := by
        simp only [enorm_mul]
        exact lintegral_mul_const' _ _ enorm_ne_top
      _ = (∑ t, ENNReal.ofReal (c t) * ‖H₀ (k t).val‖ₑ) * ‖w a‖ₑ := by rw [habs]
      _ = ∑ t, ENNReal.ofReal (c t) * ‖S t‖ₑ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro t _
        rw [mul_assoc, ← enorm_mul, hpoint]

end Langlands.AllField.RankinSelberg
