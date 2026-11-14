import Langlands.Representation.RankinSelberg.EqualRankRankOneExtensionSpanComparisonStatement
import Langlands.AllField.Representation.RankinSelberg.PadicPairFactors
import Langlands.AllField.Representation.Shahidi.Induction
/-!
# Equal-rank rank-one extension Laurent-span comparison

An internal comparison for the equal-rank rank-one extension divisibility
target: every corank-one zeta value of `π × σ₁` lies in the Laurent span of
the equal-rank zeta values of `π` against the actual upper normalized
induction of `(χ, σ₁)`. It is derived from JPSS (1983), Proposition 9.1,
printed 452–454, and the last-row reduction of printed 449, displays (1)
and (3). This module only defines the proposition.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankRankOneExtensionSpanComparisonStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

/-- The equal-rank rank-one extension Laurent-span comparison. For `π` on
`GL_(t+2)` and `σ₁` on `GL_(t+1)`, both of Whittaker type, the Laurent span of
the actual block `j = k = 0` zeta values of `π × σ₁` is contained in the
Laurent span of the actual equal-rank zeta values of `π`, transported along
`t + 1 = 1 + t`, against the published upper normalized induction in the
ordered blocks `(χ, σ₁)`. This holds for all compatible quotient measures on
both sides. Only the rank-one carrier is lifted to the universe of `σ₁`. No
induced Whittaker-type, polynomial-existence or irreducibility premise is
imposed. -/
def EqualRankRankOneExtensionSpanComparisonStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : letI := borel F
      AdditiveHaarMeasure F)
    (t : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (t + 2) F) V)
    (σ₁ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W)
    (χ : Quasicharacter F),
    (IsOfWhittakerType (t + 1) (standardCharacter ψ (t + 1)) π) →
    (IsOfWhittakerType t (standardCharacter ψ t) σ₁) →
    let χlift : Representation ℂ (Langlands.GeneralLinear 1 F)
        (ULift.{uW} ℂ) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp
        (rankOneCharacter (χ : Fˣ →* ℂˣ))
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (t + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear (t + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (t + 1) F)
    letI : BorelSpace (upperUnipotent (t + 1) F) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient t F)
    letI := borel (Langlands.GeneralLinear ((1 + t) + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear ((1 + t) + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent ((1 + t) + 1) F)
    letI : BorelSpace (upperUnipotent ((1 + t) + 1) F) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient (1 + t) F)
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F t)],
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F (1 + t))],
    ∀ (μbase : Measure (LeftUnipotentQuotient t F))
      (μind : Measure (LeftUnipotentQuotient (1 + t) F)),
      IsCompatible (upperUnipotent (t + 1) F)
        (generalLinearHaar F t) (unipotentHaar F t) μbase →
      IsCompatible (upperUnipotent ((1 + t) + 1) F)
        (generalLinearHaar F (1 + t)) (unipotentHaar F (1 + t)) μind →
      ∀ hrn : t + 1 = 1 + t,
        zetaSpan (unequalRankZetaValuesAt (r := t + 1) (n := t) 0 0 rfl
          (⟨⟩ : LocalFieldData F).residueCardinality ψ
          (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) μbase
          (rectangularMeasure ν 0 (t + 1)) π σ₁) ≤
        zetaSpan (equalRankZetaValues (n := 1 + t)
          (⟨⟩ : LocalFieldData F).residueCardinality ψ
          (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) μind
          (hrn ▸ π : Representation ℂ (Langlands.GeneralLinear ((1 + t) + 1) F) V)
          ((⟨⟩ : LocalFieldData F).normalizedProductInduced
            (Shahidi.twoBlocks 1 (t + 1) (Nat.succ_pos 0) (Nat.succ_pos t))
            (Shahidi.pairFamily χlift σ₁)))

end Langlands.AllField.RankinSelberg
