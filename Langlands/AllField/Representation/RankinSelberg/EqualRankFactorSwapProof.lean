import Langlands.Representation.RankinSelberg.EqualRankFactorSwapProof
import Langlands.AllField.Representation.RankinSelberg.EqualRankCharacterChange
import Langlands.AllField.Representation.RankinSelberg.EqualRankFactorSwapStatement
import Langlands.AllField.Representation.RankinSelberg.EqualRankSwapFactors
/-! Equal-rank L exchange by inverse-character commutation and character transport. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding CharacterChangeCompatibleMeasureStatement EqualRankAnalyticStatement EqualRankFactorSwapStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnipotentCharacterChangeModulusStatement characterChangeCompatibleMeasure characterChangeCompatibleMeasure_of_unipotentModulus equalRankFactorSwap isEqualRankLPolynomial_characterChange_normalized isPadicPairEpsilonFactor_swap_equalRank isPadicPairGammaFactor_swap_equalRank isPadicPairLPolynomial_swap_equalRank isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt leviModulus_characterChangeLevi leviModulus_characterChangeLevi_eq_pow normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow unipotentCharacterChangeModulus zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

section Commutation


end Commutation

section Padic


/-- Equal-rank p-adic L certificates are preserved at the same character and
the same supplied additive Haar measure. No factor existence is required. -/
theorem isPadicPairLPolynomial_swap_equalRank
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : letI := borel F
      AdditiveHaarMeasure F)
    {n : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) (P : ℂ[X]) :
    IsPadicPairLPolynomial F ψ ν π σ P ↔
      IsPadicPairLPolynomial F ψ ν σ π P := by
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  refine and_congr Iff.rfl (forall_congr' fun _ => forall_congr' fun μ => ?_)
  refine imp_congr_right fun hμ => ?_
  rw [isPairLPolynomial_self, isPairLPolynomial_self]
  have hLaw := characterChangeCompatibleMeasure F (⟨⟩ : LocalFieldData F) n (-1) μ hμ
  exact (isEqualRankLPolynomial_swap_inverse
    (⟨⟩ : LocalFieldData F).residueCardinality ψ
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) μ π σ P).trans
    (isEqualRankLPolynomial_characterChange_normalized (⟨⟩ : LocalFieldData F) n
      ψ (-1) μ hLaw W V σ π P).symm

end Padic

/-- Equal-rank exchange of all three certificates at the original additive
character and supplied self-dual Haar measure. -/
theorem equalRankFactorSwap : EqualRankFactorSwapStatement.{uF, uV, uW} := by
  intro F _ _ _ _ ψ ν n V hV hMV W hW hMW π σ hπ hσ
  exact ⟨fun P => isPadicPairLPolynomial_swap_equalRank F ψ ν.val π σ P,
    (fun e => isPadicPairEpsilonFactor_swap_equalRank F ψ ν.val π σ hπ hσ e),
    fun G => isPadicPairGammaFactor_swap_equalRank F ψ ν.val π σ hπ hσ G⟩

end Langlands.AllField.RankinSelberg
