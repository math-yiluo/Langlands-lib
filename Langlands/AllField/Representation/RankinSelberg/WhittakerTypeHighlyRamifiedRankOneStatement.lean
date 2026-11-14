import Langlands.AllField.Representation.RankinSelberg.WhittakerTypeHighlyRamifiedStatement
/-!
# Highly ramified L-vanishing against a character of `GL_1`

The case `r = 0` of JPSS 1983, Proposition 2.13 (printed page 404): the first
representation is a representation of `GL_1(F)` of Whittaker type and the second
one is a representation of `GL_(t+1)(F)` of Whittaker type. This is exactly the
specialization of `WhittakerTypeHighlyRamifiedLVanishingStatement` at `r = 0`,
stated over every nonarchimedean local field. No proof of the proposition is
supplied here.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerTypeHighlyRamifiedLVanishingStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear

universe uF uV uW

/-- JPSS 1983, Proposition 2.13, for a first representation of `GL_1(F)`: for a
representation `π` of `GL_1(F)` and a representation `σ` of `GL_(t+1)(F)`, both of
Whittaker type, there is a bound `A` such that every continuous quasicharacter `χ`
whose multiplicative conductor is at least `A` gives the twist `π ⊗ (χ ∘ det)`
the symmetric L-polynomial `1` against `σ`. This is
`WhittakerTypeHighlyRamifiedLVanishingStatement` with `r = 0`. -/
def WhittakerTypeHighlyRamifiedRankOneLVanishingStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ),
    ∀ (t : ℕ),
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
      {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (Langlands.GeneralLinear (0 + 1) F) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W),
    (IsOfWhittakerType 0 (standardCharacter ψ 0) π) →
    (IsOfWhittakerType t (standardCharacter ψ t) σ) →
    ∃ A : ℕ, ∀ χ : (Quasicharacter F),
      A ≤ (⟨⟩ : LocalFieldData F).multiplicativeConductor χ →
        IsPadicSymmetricLPolynomial F ψ ν.val
          (Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) π) σ 1

end Langlands.AllField.RankinSelberg
