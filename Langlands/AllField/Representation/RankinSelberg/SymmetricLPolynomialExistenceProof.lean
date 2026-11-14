import Langlands.Representation.RankinSelberg.SymmetricLPolynomialExistenceProof
import Langlands.AllField.Representation.RankinSelberg.EqualRankAnalyticProof
import Langlands.AllField.Representation.RankinSelberg.QuotientHaarExistence
import Langlands.AllField.Representation.RankinSelberg.SymmetricLPolynomialExistenceStatement
import Langlands.AllField.Representation.RankinSelberg.UnequalRankCommonGeneratorProof
/-!
# Existence of symmetric p-adic L-polynomials

The published analytic theorems give a polynomial at the canonical quotient
measure. Character transport and uniqueness of compatible quotient measures
supply the full symmetric existence statement.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankFunctionalEquationStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt SymmetricLPolynomialExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankUnitValue finiteFunctionMellin finiteFunctionShellSeries hasEqualRankCompactTest_of_kirillov iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow oneVariableMellin pairwise_disjoint_determinantSlice quotientHaarExistence quotientIwasawaIntegration quotientRootIntegration rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable symmetricLPolynomialExists unequalRankAnalytic unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIwasawaSupport unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.HarmonicAnalysis hiding PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRectangularHaarScaling padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement exists_compactOpen_glCoefficientRightStabilizer mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

private theorem inverseWhittakerType {K : Type uF} [Field K]
    [TopologicalSpace K] [IsTopologicalRing K] {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter K)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) K) V)
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π) :
    IsOfWhittakerType n (inverseStandardCharacter ψ n) π := by
  refine ⟨hπ.1, hπ.2.1, ?_⟩
  obtain ⟨e⟩ := hπ.2.2
  have e' : Nonempty (glFunctionals (ψ.scale (-1)) n π ≃ₗ[ℂ] ℂ) :=
    ⟨(characterChangeFunctionalEquiv ψ π (-1)).symm.trans e⟩
  rw [← standardCharacter_scale_neg_one ψ n]
  exact e'

private theorem orderedLPolynomialExists
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : letI := borel F
      AdditiveHaarMeasure F)
    {r n : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (hnr : n ≤ r)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ) :
    ∃ P : ℂ[X], IsPadicPairLPolynomial F ψ ν π σ P := by
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  have hσ' := inverseWhittakerType ψ σ hσ
  have hex : PairLPolynomialExists (⟨⟩ : LocalFieldData F).residueCardinality ψ
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
      (unipotentQuotientHaar F n) ν π σ := by
    rcases hnr.lt_or_eq with hlt | heq
    · exact (unequalRankCommonGenerator.{uF,uV,uW}
        F (⟨⟩ : LocalFieldData F) n r).pairLPolynomialExists
        (fun j k _ => unequalRankAnalytic.{uF,uV,uW} F (⟨⟩ : LocalFieldData F) n j k)
        hlt ψ
        (unipotentQuotientHaar F n)
        (unipotentQuotientHaar_isCompatible F n) ν V W π σ hπ hσ'
    · subst r
      exact (equalRankAnalytic.{uF,uV,uW}
        F (⟨⟩ : LocalFieldData F) n).pairLPolynomialExists
        ψ (unipotentQuotientHaar F n)
        (unipotentQuotientHaar_isCompatible F n) ν V W π σ hπ hσ'
  obtain ⟨P, hP⟩ := hex
  refine ⟨P, ?_, ?_⟩
  · exact quotientHaarExistence F (⟨⟩ : LocalFieldData F) n
  · intro _ μ hμ
    rw [unipotentQuotientHaar_unique F n μ hμ]
    exact hP

/-- Every pair of Whittaker-type representations has one symmetric p-adic
L-polynomial for all compatible quotient measures. -/
theorem symmetricLPolynomialExists :
    SymmetricLPolynomialExistenceStatement.{uF,uV,uW} := by
  intro F _ _ _ _ ψ ν r n V _ _ W _ _ π σ hπ hσ
  by_cases hnr : n ≤ r
  · obtain ⟨P, hP⟩ := orderedLPolynomialExists.{uF,uV,uW}
      F ψ ν.val π σ hnr hπ hσ
    exact ⟨P, by simpa only [IsPadicSymmetricLPolynomial, ite_eq_left hnr] using hP⟩
  · obtain ⟨P, hP⟩ := orderedLPolynomialExists.{uF,uW,uV}
      F ψ ν.val σ π (Nat.le_of_lt (Nat.lt_of_not_ge hnr)) hσ hπ
    exact ⟨P, by simpa only [IsPadicSymmetricLPolynomial, ite_eq_right hnr] using hP⟩

end Langlands.AllField.RankinSelberg
