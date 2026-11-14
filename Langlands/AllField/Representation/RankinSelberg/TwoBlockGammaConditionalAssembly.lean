import Langlands.Representation.RankinSelberg.TwoBlockGammaConditionalAssembly
import Langlands.AllField.Representation.RankinSelberg.RankOneWhittakerTypeStatement
import Langlands.AllField.Representation.RankinSelberg.TwoBlockGammaDescentObjects
/-! Conditional assembly in a carrier universe closed under induction. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFactorSwapStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement NormalizedProductWhittakerTypeStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement RankOneWhittakerTypeStatement TwoBlockGammaAdjacentRankStatement TwoBlockGammaDominantRankStatement TwoBlockGammaMultiplicativityStatement TwoBlockGammaRankOneStatement TwoBlockLAdjacentRankStatement TwoBlockLDominantRankStatement TwoBlockLFactorMultiplicativityStatement TwoBlockLRankOneStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerTypeGammaConstructionInputStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType twoBlockGammaAuxiliary twoBlockGammaMultiplicativity_of_inputs_commonUniverse
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis
open Langlands.Whittaker hiding functionalsCongr
open Langlands.GeneralLinear
open Langlands.RankinSelberg.TwoBlockGammaDescent hiding Object adjacent_eq allRanks_eq certificate_swap certified dominant_eq equality_of_certificates family family_type gamma gamma_cert gamma_swap induced ofRepresentation rankOne_eq
open Langlands.AllField.RankinSelberg.TwoBlockGammaDescent

universe uF u

/-- A rank-one auxiliary object obtained from the trivial scalar character.
Only the supplied scalar full-type statement establishes its full type. -/
def twoBlockGammaAuxiliary
    (hScalar : RankOneWhittakerTypeStatement.{uF})
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F) :
    Object.{uF, u} F ψ 0 := by
  let χ : Quasicharacter F := 1
  let ρ : Representation ℂ (Langlands.GeneralLinear 1 F) (ULift.{max uF u} ℂ) :=
    (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp
      (rankOneCharacter (χ : Fˣ →* ℂˣ))
  have e : (rankOneCharacter (χ : Fˣ →* ℂˣ)).Equiv ρ :=
    Representation.Equiv.mk ULift.moduleEquiv.symm (by intro g; rfl)
  exact ofRepresentation ρ ((hScalar F ψ χ).of_equiv e)

/-- The seven explicit analytic/full-type inputs imply the exact two-block
gamma proposition in a stable common carrier universe. This is conditional
assembly, with no claim that any input has been proved. -/
theorem twoBlockGammaMultiplicativity_of_inputs_commonUniverse
    (hInd : NormalizedProductWhittakerTypeStatement.{uF, max uF u})
    (hInput : WhittakerTypeGammaConstructionInputStatement.{uF, max uF u, max uF u})
    (hSwap : EqualRankFactorSwapStatement.{uF, max uF u, max uF u})
    (hDominant : TwoBlockGammaDominantRankStatement.{uF, max uF u, max uF u})
    (hAdjacent : TwoBlockGammaAdjacentRankStatement.{uF, max uF u, max uF u})
    (hRankOne : TwoBlockGammaRankOneStatement.{uF, max uF u, max uF u})
    (hScalar : RankOneWhittakerTypeStatement.{uF}) :
    TwoBlockGammaMultiplicativityStatement.{uF, max uF u, max uF u} := by
  intro F _ _ _ _ ψ ν r t m h V hVAdd hVMod W hWAdd hWMod pi sigma hpi hsigma
  exact certified ν hInd hInput hSwap hDominant hAdjacent hRankOne
    (twoBlockGammaAuxiliary hScalar F ψ) r t m h pi sigma hpi hsigma

end Langlands.AllField.RankinSelberg
