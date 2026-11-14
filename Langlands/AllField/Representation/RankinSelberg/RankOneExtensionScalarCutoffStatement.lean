import Langlands.Representation.RankinSelberg.RankOneExtensionScalarCutoffStatement
import Langlands.AllField.Representation.RankinSelberg.RankOneExtensionAnalyticData
/-!
# Same-model scalar Fourier cutoff for the early JPSS Lemma (5.5)

JPSS (1983), Lemma (5.5), formula (9) and its proof, printed 426–427: right
smearing by the one-coordinate transvection against a Schwartz–Bruhat weight
whose plus-sign Fourier transform is the cut-off inverse quasicharacter.
The small-neighborhood refinement replacing `a` by `1` inside the original
coefficient is derived, as explained in the paired Markdown. This module only
defines the proposition.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement RankOneExtensionLDivisibilityStatement RankOneExtensionScalarCutoffStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneExtensionLowerFamily rankOneExtensionLowerInduced rankOneExtensionLowerModel rankOneExtensionLowerSection rankOneExtensionLowerSectionCoefficient rankOneExtensionLowerSectionEval rankOneExtensionLowerToUpperEquiv rankOneExtensionWhittakerContraction rankOneWhittakerType
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding functionalsCongr

universe uF uV

/-- For every open neighborhood `O` of `1`, there are a compact open set
`U ⊆ O` of normalized absolute value one containing `1`, an actual
Schwartz–Bruhat pair `κ, Φ` with `Φ = fourierIntegral ψ ν κ` everywhere,
`Φ 0 = 0` and `Φ a = χ(a)⁻¹` on units in `U`, zero on other units, and one
coefficient `f₁` in the same coefficient model as `f₂`. The coefficient `f₁`
is the global right `κ`-smearing of `f₂` along
`rankOneExtensionSmearingUnipotent t k`, it equals `Φ(a) f₂` on every embedded
lower block `B(a)`, `U` is small enough that `f₂(B(a)) = f₂(B(1))` for
`a ∈ U`, and hence `f₁(B(a))` is `χ(a)⁻¹ f₂(B(1))` on `U` and zero otherwise.
This is a closed proposition definition, not a proof. -/
def RankOneExtensionScalarCutoffStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (t k : ℕ)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ
      (Langlands.GeneralLinear ((1 + (t + 1)) + (k + 1)) F) V),
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    IsSmooth π →
    ∀ (ℓ : glFunctionals ψ ((1 + (t + 1)) + k) π)
      (f₂ : (coefficientModel π ℓ).toSubmodule)
      (χ : Quasicharacter F)
      (O : Set F), IsOpen O → (1 : F) ∈ O →
      ∃ (U : Set F) (κ Φ : SchwartzBruhat F)
        (f₁ : (coefficientModel π ℓ).toSubmodule),
        IsCompact U ∧ IsOpen U ∧ U ⊆ O ∧ (1 : F) ∈ U ∧ (0 : F) ∉ U ∧
        (∀ y ∈ U, normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) y = 1) ∧
        Φ 0 = 0 ∧
        (∀ a : Fˣ, (a : F) ∈ U →
          Φ (a : F) = ((χ a : ℂˣ) : ℂ)⁻¹) ∧
        (∀ a : Fˣ, (a : F) ∉ U → Φ (a : F) = 0) ∧
        (∀ b : F, Φ b = fourierIntegral ψ ν.val κ b) ∧
        (∀ h : Langlands.GeneralLinear ((1 + (t + 1)) + (k + 1)) F,
          Integrable
            (fun u => κ u * f₂.val.val (h * rankOneExtensionSmearingUnipotent t k u))
            ν.val.measure ∧
          f₁.val.val h =
            ∫ u, κ u * f₂.val.val (h * rankOneExtensionSmearingUnipotent t k u)
              ∂ν.val.measure) ∧
        (∀ (m : Langlands.GeneralLinear (t + 1) F)
          (x : Fin (t + 1) → F) (a : Fˣ),
          f₁.val.val (rankOneExtensionEmbeddedLowerBlock t k m x a) =
            Φ (a : F) *
              f₂.val.val (rankOneExtensionEmbeddedLowerBlock t k m x a)) ∧
        (∀ (m : Langlands.GeneralLinear (t + 1) F)
          (x : Fin (t + 1) → F) (a : Fˣ), (a : F) ∈ U →
          f₂.val.val (rankOneExtensionEmbeddedLowerBlock t k m x a) =
            f₂.val.val (rankOneExtensionEmbeddedLowerBlock t k m x 1)) ∧
        (∀ (m : Langlands.GeneralLinear (t + 1) F)
          (x : Fin (t + 1) → F) (a : Fˣ), (a : F) ∈ U →
          f₁.val.val (rankOneExtensionEmbeddedLowerBlock t k m x a) =
            ((χ a : ℂˣ) : ℂ)⁻¹ *
              f₂.val.val (rankOneExtensionEmbeddedLowerBlock t k m x 1)) ∧
        ∀ (m : Langlands.GeneralLinear (t + 1) F)
          (x : Fin (t + 1) → F) (a : Fˣ), (a : F) ∉ U →
          f₁.val.val (rankOneExtensionEmbeddedLowerBlock t k m x a) = 0

end Langlands.AllField.RankinSelberg
