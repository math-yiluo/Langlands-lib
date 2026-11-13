import Langlands.Representation.RankinSelberg.UnequalRankCommonGeneratorProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankAnalyticProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankBlockSpanProof
/-! A normalized reciprocal polynomial common to every unequal-rank JPSS block. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding FiniteFunctionMellinStatement FiniteFunctionShellSeriesStatement IwasawaTorusPartitionStatement IwasawaTorusSumStatement ModelAsymptoticTransferStatement OneVariableMellinStatement QuotientIwasawaIntegrationStatement QuotientRootIntegrationStatement RootCoordinateChangeStatement RootCoordinateFiniteFunctionStatement RootSpectralWeightStatement UnequalRankAdjacentBlockSpanStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnequalRankCompactSupportStatement UnequalRankFiniteExpansionStatement UnequalRankFourierSmearingStatement UnequalRankFunctionalEquationStatement UnequalRankIwasawaSupportStatement UnequalRankMirabolicUnitTestStatement UnequalRankUnitSpanStatement UnequalRankZeroRowAnalyticStatement UnequalRankZeroRowNormalizedCompactIntegrationStatement UnequalRankZeroRowRootExpansionStatement ValuationShellIntegrationStatement continuous_ord_units diagonalConj_map diagonal_abs_bound diagonal_abs_last exists_compactOpen_rectangular_subgroup finiteFunctionMellin finiteFunctionShellSeries iwasawaTorusPartition iwasawaTorusSum modelAsymptoticTransfer normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply oneVariableMellin quotientIwasawaIntegration quotientRootIntegration rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight singleton_modulus_real unequalRankAdjacentBlockSpan unequalRankAnalytic unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankFiniteExpansion_of_cosetExpansion unequalRankFourierSmearingStatement unequalRankIwasawaSupport unequalRankMirabolicUnitTest unequalRankUnitSpan unequalRankZeroRowAnalytic unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unequalRank_coefficient_invariant valuationShellIntegration
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicLatticeFourierStatement PadicLatticeGeometryStatement PadicLatticeHaarStatement PadicLatticeSchwartzExpansionStatement PadicRectangularHaarScalingStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement SchwartzBruhatValuationBoundsStatement padicLatticeFourier padicLatticeGeometry padicLatticeHaar padicLatticeSchwartzExpansion padicRectangularHaarScaling padicRectangularHaarScalingStatement padicRowFourierSurjectivity padicScalarHaarScaling padicSchwartzBruhat_exists_additiveLattice_invariant padicSelfDualMeasureExists schwartzBruhatValuationBounds
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CoordinateJacquetKernelStatement JPSBoundedDilationRecurrenceStatement JPSCoordinateUnitInvarianceStatement JPSDecompositionStatement JPSDilationAssemblyStatement JPSUniformDilationStatement MirabolicCompactMinimalityStatement ModelKirillovTransferStatement SmoothSimpleRootSupportStatement coordinateJacquetKernelStatement jpsBoundedDilationRecurrence jpsCoordinateUnitInvariance jpsDecomposition jpsDilationAssembly jpsUniformDilation mirabolicCompactMinimality modelKirillovTransfer smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration

/-- Finite induction transports a block-zero generator through adjacent spans. -/
private theorem commonGenerator_of_adjacentSpan {n r : ℕ} (hnr : n < r)
    (values : (j k : ℕ) → r = n + (j + k + 1) → Set RationalFunctions)
    (hbase : NormalizedGeneratorExists (values 0 (r - n - 1) (by omega)))
    (hstep : ∀ (j k : ℕ) (hr : r = n + (j + k + 2)),
      zetaSpan (values (j + 1) k (by omega)) =
        zetaSpan (values j (k + 1) (by omega))) :
    ∃ P : Polynomial ℂ, ∀ (j k : ℕ) (hr : r = n + (j + k + 1)),
      IsNormalizedGenerator (values j k hr) P := by
  obtain ⟨P, hP⟩ := hbase
  refine ⟨P, ?_⟩
  intro j
  induction j with
  | zero =>
      intro k hr
      have hk : k = r - n - 1 := by omega
      subst k
      exact hP
  | succ j ih =>
      intro k hr
      have hspan := hstep j k (by omega)
      have hgen := ih (k + 1) (by omega)
      exact ⟨hgen.1, hspan.trans hgen.2⟩

/-- JPSS Theorem 2.7(ii): one normalized reciprocal polynomial generates every
allowed block at fixed unequal ranks, for the supplied topology and measures. -/
theorem unequalRankCommonGenerator.{uF,uV,uW} 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n r : ℕ) :
    UnequalRankCommonGeneratorStatement.{uF,uV,uW} F T n r := by
  have hanalytic : ∀ j k, UnequalRankAnalyticStatement.{uF,uV,uW} F T n j k :=
    fun j k => unequalRankAnalytic.{uF,uV,uW} F T n j k
  have hadjacent := unequalRankAdjacentBlockSpan.{uF,uV,uW} F T n r
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  dsimp only [UnequalRankCommonGeneratorStatement,
    UnequalRankAnalyticStatement, UnequalRankAdjacentBlockSpanStatement] at *
  intro hnr ψ hright μ hμ ν V instV modV W instW modW π σ hπ hσ ℓ ℓ' hℓ hℓ'
  have hbase : NormalizedGeneratorExists
      (unequalRankValuesAt 0 (r - n - 1) (by omega) T.residueCardinality ψ
        (normalizedAbsoluteValue T) μ (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ') := by
    have hgeneral : ∀ (r : ℕ) (hr : r = n + (0 + (r - n - 1) + 1))
        (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V),
        IsOfWhittakerType r (standardCharacter ψ r) π →
        ∀ (ℓ : glFunctionals ψ r π), ℓ.val ≠ 0 →
        NormalizedGeneratorExists
          (unequalRankValuesAt 0 (r - n - 1) hr T.residueCardinality ψ
            (normalizedAbsoluteValue T) μ (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ') := by
      intro r hr π hπ ℓ hℓ
      generalize hk : r - n - 1 = k at *
      subst r
      exact (hanalytic 0 k ψ μ hμ ν V W π σ hπ hσ ℓ ℓ' hℓ hℓ').2.2.2
    exact hgeneral r (by omega) π hπ ℓ hℓ
  exact commonGenerator_of_adjacentSpan hnr
    (fun j k hr => unequalRankValuesAt j k hr T.residueCardinality ψ
      (normalizedAbsoluteValue T) μ (rectangularMeasure ν j (n + 1)) π σ ℓ ℓ')
    hbase (hadjacent hnr ψ μ hμ ν V W π σ hπ hσ ℓ ℓ' hℓ hℓ')

end Langlands.AllField.RankinSelberg
