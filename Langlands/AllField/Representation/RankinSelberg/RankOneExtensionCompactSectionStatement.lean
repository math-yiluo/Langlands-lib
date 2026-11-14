import Langlands.Representation.RankinSelberg.RankOneExtensionCompactSectionStatement
import Langlands.AllField.Representation.RankinSelberg.RankOneExtensionAnalyticData
/-!
# Normalized compact sections for the strict rank-one extension

JPSS (1983), Lemma (5.5), printed 424–425, formulas (5)–(7): an actual section of
the lower induction of `(σ, χ)`, supported in the lower opposite parabolic times the
complementary upper cell, whose restriction to that cell is a normalized compact test
function times a fixed pure tensor, with the test function supported where the
supplied vector of `π` is fixed. This module only defines the proposition.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement RankOneExtensionCompactSectionStatement RankOneExtensionLDivisibilityStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneExtensionLowerFamily rankOneExtensionLowerInduced rankOneExtensionLowerModel rankOneExtensionLowerSection rankOneExtensionLowerSectionCoefficient rankOneExtensionLowerSectionEval rankOneExtensionLowerToUpperEquiv rankOneExtensionWhittakerContraction rankOneWhittakerType
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF uV uW

/-- The normalized compact-section construction of the early JPSS Lemma (5.5)
argument, in the strict rank range `t + 3 ≤ r + 1` with `r + 1 = (1 + (t + 1)) + (k + 1)`.
For every open neighbourhood `O` of zero in the row space `Fin (t + 1) → F`, there are a
Schwartz–Bruhat function `φ` supported in `O` with integral one for the supplied
self-dual row measure, and an actual section `f` of the published lower induction of
`(σ, χ)` such that `f (u(y)) = φ y • (w ⊗ 1)` on the upper cell, `f` vanishes off
`P̄ · u(supp φ)`, and every `y ∈ supp φ` fixes `v` under `π (diag(u(y), I_(k+1)))`. -/
def RankOneExtensionCompactSectionStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (t k : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear ((1 + (t + 1)) + (k + 1)) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W)
    (χ : Quasicharacter F)
    (v : V) (w : W),
    (IsSmooth π) →
    (IsSmooth σ) →
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    ∀ O : Set (Fin (t + 1) → F), IsOpen O → (0 : Fin (t + 1) → F) ∈ O →
      ∃ (φ : SchwartzBruhat (Fin (t + 1) → F))
        (f : rankOneExtensionLowerSection F t χ σ),
        Function.support φ ⊆ O ∧
        Integrable φ (rowMeasure ν.val (t + 1)) ∧
        ∫ y, φ y ∂rowMeasure ν.val (t + 1) = 1 ∧
        (∀ y : Fin (t + 1) → F,
          rankOneExtensionLowerSectionEval F t χ σ f (rankOneExtensionUpperCell t y) =
            φ y • rankOneExtensionLowerPureTensor w (ULift.up 1)) ∧
        (∀ g : Langlands.GeneralLinear (1 + (t + 1)) F,
          rankOneExtensionLowerSectionEval F t χ σ f g ≠ 0 →
            ∃ q : (rankOneExtensionLowerShape t).oppositeParabolic F,
              ∃ y ∈ Function.support φ,
                g = (q : Langlands.GeneralLinear (1 + (t + 1)) F) *
                  rankOneExtensionUpperCell t y) ∧
        (∀ y ∈ Function.support φ,
          π (rankInclusion (k + 1) (rankOneExtensionUpperCell t y)) v = v)

end Langlands.AllField.RankinSelberg
