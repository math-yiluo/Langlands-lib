import Langlands.Representation.RankinSelberg.EqualRankRankOneExtensionDivisibilityStatement
import Langlands.AllField.Representation.RankinSelberg.PadicPairFactors
import Langlands.AllField.Representation.Shahidi.Induction
/-!
# Equal-rank rank-one extension reverse divisibility

An internal prerequisite for the first general-rank descent step in JPSS
section 7.2. The test and induced ranks are both `t + 2`, beyond the rank
range printed in Lemma (5.5). This module only defines the proposition;
it supplies neither its proof nor the equal-rank analytic comparison.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankRankOneExtensionLDivisibilityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.Polynomial
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear

universe uF uV uW

/-- The equal-rank reverse L-polynomial divisibility prerequisite for the
actual upper normalized induction in ordered blocks `(χ, σ₁)`. Both
certified polynomials are conclusions. The only representation hypotheses
are Whittaker type of `π` and `σ₁`; their carriers and the field have
independent universes. This is an internal statement target, not the
literal rank-restricted JPSS Lemma (5.5). -/
def EqualRankRankOneExtensionLDivisibilityStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
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
    ∃ Pbase Pind : ℂ[X],
      IsPadicSymmetricLPolynomial F ψ ν.val π σ₁ Pbase ∧
      IsPadicSymmetricLPolynomial F ψ ν.val π
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced
          (Shahidi.twoBlocks 1 (t + 1) (Nat.succ_pos 0) (Nat.succ_pos t))
          (Shahidi.pairFamily χlift σ₁)) Pind ∧
      Pbase ∣ Pind

end Langlands.AllField.RankinSelberg
