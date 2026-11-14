import Langlands.Representation.RankinSelberg.EqualRankAnalyticProof
import Langlands.AllField.LocalField.SmoothCharacterNormProofSupplement
import Langlands.AllField.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.AllField.Representation.Geometric.GeometricLemmaStatement
import Langlands.AllField.Representation.Parabolic.NormalizedJacquetStatementSupplement
import Langlands.AllField.Representation.RankinSelberg.DeterminantSlicesSupplement
import Langlands.AllField.Representation.RankinSelberg.EqualRankUnitValueProof
import Langlands.AllField.Representation.RankinSelberg.FiniteFunctionMellinProof
import Langlands.AllField.Representation.RankinSelberg.ModelAsymptoticProof
import Langlands.AllField.Representation.RankinSelberg.QuotientAnalyticProof
import Langlands.AllField.Representation.RankinSelberg.QuotientIwasawaIntegrationProof
import Langlands.AllField.Representation.Unramified.SphericalConstituentExistenceProof
import Langlands.AllField.Representation.Whittaker.TypeAsymptoticProof
/-!
# Equal-rank JPSS convergence, rationality and normalized generator

Combine the full Whittaker expansion, finite-function Mellin analysis and quotient
Iwasawa integration with an actual unit-value test and Laurent normalization.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankFunctionalEquationStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankUnitValue finiteFunctionMellin finiteFunctionShellSeries hasEqualRankCompactTest_of_kirillov iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice iwasawaTorusSum lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow oneVariableMellin pairwise_disjoint_determinantSlice quotientIwasawaIntegration quotientRootIntegration rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement exists_compactOpen_glCoefficientRightStabilizer mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

/-- Equal-rank convergence, rational continuation, a common Laurent denominator
and a normalized reciprocal-polynomial generator for actual JPSS integrals. -/
theorem equalRankAnalytic
    (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ) :
    EqualRankAnalyticStatement.{uF, uV, uW} F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  intro ψ _ μ hμ V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ'
  have hexpπ := modelAsymptoticTransfer whittakerTypeAsymptotic.{uF, uV}
    F T n V π ψ (standardCharacter ψ n) (Or.inl rfl) hπ
  have hexpσ := modelAsymptoticTransfer whittakerTypeAsymptotic.{uF, uW}
    F T n W σ ψ (inverseStandardCharacter ψ n) (Or.inr rfl) hσ
  obtain ⟨D, hD, hdata⟩ :=
    equalRankQuotientAnalytic F T n finiteFunctionMellin.{uF}
      (quotientIwasawaIntegration F T n) V W π σ ψ
      hπ.1.1 hσ.1.1 hexpπ hexpσ
  obtain ⟨hconv, hrat, hclear⟩ := hdata ℓ ℓ' μ hμ
  have hden : HasCommonDenominator
      (equalRankRationalValues T.residueCardinality ψ
        (normalizedAbsoluteValue T) μ π σ ℓ ℓ') := ⟨D, hD, hclear⟩
  have hone := equalRankUnitValue.{uF, uV, uW} F T n ψ μ hμ
    V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
  exact ⟨hconv, hrat, hden,
    normalizedGeneratorExistence _ hden (mem_zetaSpan hone)⟩

end Langlands.AllField.RankinSelberg
