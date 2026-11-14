import Langlands.Representation.RankinSelberg.SymmetricGammaExpressionProof
import Langlands.AllField.LocalFactor.ResidueReflection
import Langlands.AllField.Representation.RankinSelberg.GammaFromWhittakerType
/-!
# The canonical expression characterizes symmetric gamma certificates

The original and dual analytic inputs remain in the construction premise.
The supplied intrinsic polynomial certificates determine the rational expression.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

set_option maxHeartbeats 800000 in
/-- Arbitrary certified epsilon data and original/dual polynomials give the
canonical gamma certificate for an ordered pair under its construction input. -/
theorem IsPadicPairEpsilonFactor.gammaFactor_of_constructionInput
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : letI := borel F
      AdditiveHaarMeasure F)
    {r n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (h : PadicPairGammaConstructionInput F ψ ν π σ)
    {e : ℂˣ × ℤ} {P Pdual : ℂ[X]}
    (he : IsPadicPairEpsilonFactor F ψ ν π σ e)
    (hP : IsPadicPairLPolynomial F ψ ν π σ P)
    (hPd : IsPadicPairLPolynomial F (ψ.scale (-1)) ν
      (inverseTransposePullback π) (inverseTransposePullback σ) Pdual) :
    IsPadicPairGammaFactor F ψ ν π σ
      (rationalGammaExpression (Langlands.AllField.LocalFactor.residueReflection F) e.1 e.2 P Pdual) := by
  let := (⟨⟩ : LocalFieldData F).fieldT2
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  obtain ⟨hnr, _, _, hπ, hσ, hA, hAd⟩ := h
  have hπd := isOfWhittakerType_firstDual ψ π hπ
  have hσd := isOfWhittakerType_secondDual ψ σ hσ
  have hμ := unipotentQuotientHaar_isCompatible F n
  have hP' := hP.2 (unipotentQuotientHaar F n) hμ
  have hPd' := hPd.2 (unipotentQuotientHaar F n) hμ
  have hq := (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
  change IsPairGammaFactor _ _ _ _ _ _ _
  by_cases hr : r = n
  · subst r
    simp only [PairAnalyticInput] at hA hAd
    apply isPairGammaFactor_self.mpr
    exact IsEqualRankEpsilonFactor.gammaFactor hπ hσ hπd hσd hA
      (fun ℓ ℓ' hℓ hℓ' => hAd _ _ (firstDualFunctional_ne_zero ψ π hℓ)
        (secondDualFunctional_ne_zero ψ σ hℓ'))
      hq (Langlands.AllField.LocalFactor.coe_residueReflection F) hμ
      (isPairEpsilonFactor_self.mp he)
      (isPairLPolynomial_self.mp hP') (isPairLPolynomial_self.mp hPd')
  · have hlt : n < r := by omega
    simp only [PairAnalyticInput, dite_eq_right hr] at hA hAd
    apply (isPairGammaFactor_of_lt hlt).mpr
    exact IsUnequalRankEpsilonFactor.gammaFactor hlt hπ hσ hπd hσd hA
      (fun ℓ ℓ' hℓ hℓ' => hAd _ _ (firstDualFunctional_ne_zero ψ π hℓ)
        (secondDualFunctional_ne_zero ψ σ hℓ'))
      hq (Langlands.AllField.LocalFactor.coe_residueReflection F) hμ
      ((isPairEpsilonFactor_of_lt hlt).mp he) hP' hPd'

end Langlands.AllField.RankinSelberg
