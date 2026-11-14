import Langlands.Representation.RankinSelberg.RankOneExtensionSpanComparisonStatement
import Langlands.AllField.Representation.RankinSelberg.RankOneExtensionTransport
/-!
# Strict rank-one extension Laurent-span comparison

JPSS (1983), Lemma (5.5), printed 423–427: in the strict rank range, every
block-one zeta value of `π × σ₁` lies in the Laurent span of the block-zero
zeta values of `π` against the actual lower induction `(σ₁, χ)`. This module
only defines the proposition.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement RankOneExtensionLDivisibilityStatement RankOneExtensionSpanComparisonStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneExtensionLowerFamily rankOneExtensionLowerInduced rankOneExtensionLowerToUpperEquiv
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

/-- The early JPSS Lemma (5.5) comparison in its original strict rank range
`t + 3 ≤ r + 1`. The Laurent span of the actual block-one zeta values of
`π × σ₁`, with predecessor rank `t`, is contained in the Laurent span of the
actual block-zero zeta values of `π` against the published lower induction of
`(σ₁, χ)`, with predecessor rank `1 + t`. Both sides have the same trailing
index `r - t - 2`. Only the rank-one carrier is lifted to the universe of `σ₁`.
No induced Whittaker-type, polynomial-existence or irreducibility premise is
imposed. -/
def RankOneExtensionSpanComparisonStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (r t : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ₁ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W)
    (χ : Quasicharacter F)
    (hrt : t + 3 ≤ r + 1),
    (IsOfWhittakerType r (standardCharacter ψ r) π) →
    (IsOfWhittakerType t (standardCharacter ψ t) σ₁) →
    let χlift : Representation ℂ (Langlands.GeneralLinear 1 F)
        (ULift.{uW} ℂ) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp
        (rankOneCharacter (χ : Fˣ →* ℂˣ))
    let hrBase : r = t + (1 + (r - t - 2) + 1) := by omega
    let hrInd : r = (1 + t) + (0 + (r - t - 2) + 1) := by omega
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (t + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear (t + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (t + 1) F)
    letI : BorelSpace (upperUnipotent (t + 1) F) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient t F)
    letI : BorelSpace (LeftUnipotentQuotient t F) := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear ((1 + t) + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear ((1 + t) + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent ((1 + t) + 1) F)
    letI : BorelSpace (upperUnipotent ((1 + t) + 1) F) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient (1 + t) F)
    letI : BorelSpace (LeftUnipotentQuotient (1 + t) F) := ⟨rfl⟩
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F t)],
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F (1 + t))],
    ∀ (μbase : Measure (LeftUnipotentQuotient t F))
      (μind : Measure (LeftUnipotentQuotient (1 + t) F)),
      IsCompatible (upperUnipotent (t + 1) F)
        (generalLinearHaar F t) (unipotentHaar F t) μbase →
      IsCompatible (upperUnipotent ((1 + t) + 1) F)
        (generalLinearHaar F (1 + t)) (unipotentHaar F (1 + t)) μind →
      zetaSpan (unequalRankZetaValuesAt (r := r) (n := t) 1 (r - t - 2) hrBase
        (⟨⟩ : LocalFieldData F).residueCardinality ψ
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) μbase
        (rectangularMeasure ν.val 1 (t + 1)) π σ₁) ≤
      zetaSpan (unequalRankZetaValuesAt (r := r) (n := 1 + t) 0 (r - t - 2) hrInd
        (⟨⟩ : LocalFieldData F).residueCardinality ψ
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) μind
        (rectangularMeasure ν.val 0 ((1 + t) + 1)) π
        (rankOneExtensionLowerInduced F t χlift σ₁))

end Langlands.AllField.RankinSelberg
