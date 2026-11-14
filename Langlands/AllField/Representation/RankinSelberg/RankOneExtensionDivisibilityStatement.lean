import Langlands.Representation.RankinSelberg.RankOneExtensionDivisibilityStatement
import Langlands.AllField.Representation.RankinSelberg.PadicPairFactors
import Langlands.AllField.Representation.Shahidi.Induction
/-!
# Restricted rank-one extension divisibility

JPSS (1983), Lemma (5.5), transported from lower induction `(σ₁, χ)` to
upper induction `(χ, σ₁)`. The test rank is at least two greater than the
rank of `σ₁`. Both certified L-polynomials exist, and the base polynomial
divides the induced polynomial. This module only defines the proposition.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement RankOneExtensionLDivisibilityStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.Polynomial
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear

universe uF uV uW

/-- The upper-parabolic form of JPSS Lemma (5.5), restricted to its original
rank range. The upper blocks are ordered `(χ, σ₁)`. Only the rank-one carrier
is lifted to the universe of `σ₁`, by conjugating the existing rank-one action
through the canonical linear equivalence. No induced Whittaker-type or
factor-existence premise is imposed. -/
def RankOneExtensionLDivisibilityStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (r t : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ₁ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W)
    (χ : Quasicharacter F),
    t + 3 ≤ r + 1 →
    (IsOfWhittakerType r (standardCharacter ψ r) π) →
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
