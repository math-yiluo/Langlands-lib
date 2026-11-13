import Langlands.Representation.RankinSelberg.UnequalRankAnalyticProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankCompactSupportProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankFiniteExpansionProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankUnitSpanProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankZeroRowAnalyticProof
/-!
# JPSS unequal-rank convergence, rationality and normalized generators

Transfer the published zero-row analytics through the published compact
rectangular expansion, retaining the actual coefficient models and measures.
The published unit-span and algebraic normalization theorems supply the
normalized generator for each block.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding FiniteFunctionMellinStatement FiniteFunctionShellSeriesStatement IwasawaTorusPartitionStatement IwasawaTorusSumStatement ModelAsymptoticTransferStatement OneVariableMellinStatement QuotientIwasawaIntegrationStatement QuotientRootIntegrationStatement RootCoordinateChangeStatement RootCoordinateFiniteFunctionStatement RootSpectralWeightStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnequalRankCompactSupportStatement UnequalRankFiniteExpansionStatement UnequalRankFunctionalEquationStatement UnequalRankIwasawaSupportStatement UnequalRankMirabolicUnitTestStatement UnequalRankUnitSpanStatement UnequalRankZeroRowAnalyticStatement UnequalRankZeroRowNormalizedCompactIntegrationStatement UnequalRankZeroRowRootExpansionStatement ValuationShellIntegrationStatement continuous_ord_units diagonalConj_map diagonal_abs_bound diagonal_abs_last exists_compactOpen_rectangular_subgroup finiteFunctionMellin finiteFunctionShellSeries iwasawaTorusPartition iwasawaTorusSum modelAsymptoticTransfer normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply oneVariableMellin quotientIwasawaIntegration quotientRootIntegration rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight singleton_modulus_real unequalRankAnalytic unequalRankCompactSupport unequalRankFiniteExpansion unequalRankFiniteExpansion_of_cosetExpansion unequalRankIwasawaSupport unequalRankMirabolicUnitTest unequalRankUnitSpan unequalRankZeroRowAnalytic unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unequalRank_coefficient_invariant valuationShellIntegration
open Langlands.AllField.RankinSelberg

open MeasureTheory Polynomial
open scoped BigOperators

namespace UnequalRankReduction
open Langlands.RankinSelberg.UnequalRankReduction hiding padic_rectangular_schwartz_integrable unequalRankAnalytic_of_prerequisites unequalRankAnalytic_of_zero_row
open Langlands.AllField.RankinSelberg.UnequalRankReduction
open Langlands.RankinSelberg hiding FiniteFunctionMellinStatement FiniteFunctionShellSeriesStatement IwasawaTorusPartitionStatement IwasawaTorusSumStatement ModelAsymptoticTransferStatement OneVariableMellinStatement QuotientIwasawaIntegrationStatement QuotientRootIntegrationStatement RootCoordinateChangeStatement RootCoordinateFiniteFunctionStatement RootSpectralWeightStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnequalRankCompactSupportStatement UnequalRankFiniteExpansionStatement UnequalRankFunctionalEquationStatement UnequalRankIwasawaSupportStatement UnequalRankMirabolicUnitTestStatement UnequalRankUnitSpanStatement UnequalRankZeroRowAnalyticStatement UnequalRankZeroRowNormalizedCompactIntegrationStatement UnequalRankZeroRowRootExpansionStatement ValuationShellIntegrationStatement continuous_ord_units diagonalConj_map diagonal_abs_bound diagonal_abs_last exists_compactOpen_rectangular_subgroup finiteFunctionMellin finiteFunctionShellSeries iwasawaTorusPartition iwasawaTorusSum modelAsymptoticTransfer normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply oneVariableMellin quotientIwasawaIntegration quotientRootIntegration rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight singleton_modulus_real unequalRankAnalytic unequalRankCompactSupport unequalRankFiniteExpansion unequalRankFiniteExpansion_of_cosetExpansion unequalRankIwasawaSupport unequalRankMirabolicUnitTest unequalRankUnitSpan unequalRankZeroRowAnalytic unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unequalRank_coefficient_invariant valuationShellIntegration
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement SchwartzBruhatValuationBoundsStatement padicRectangularHaarScaling padicRectangularHaarScalingStatement padicScalarHaarScaling schwartzBruhatValuationBounds
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CoordinateJacquetKernelStatement JPSBoundedDilationRecurrenceStatement JPSCoordinateUnitInvarianceStatement JPSDecompositionStatement JPSDilationAssemblyStatement JPSUniformDilationStatement MirabolicCompactMinimalityStatement ModelKirillovTransferStatement SmoothSimpleRootSupportStatement coordinateJacquetKernelStatement jpsBoundedDilationRecurrence jpsCoordinateUnitInvariance jpsDecomposition jpsDilationAssembly jpsUniformDilation mirabolicCompactMinimality modelKirillovTransfer smoothSimpleRootSupport
open Langlands.AllField.Whittaker

open Langlands.RankinSelberg.RationalContinuationLinear

section ActualIntegrands

variable {F : Type*} [Field F] [TopologicalSpace F]
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) {n : ℕ}

end ActualIntegrands

section CoefficientModels

universe uF uV uW

variable {F : Type uF} [Field F] [TopologicalSpace F]
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {V' : Type uW} [AddCommGroup V'] [Module ℂ V']

end CoefficientModels

section ZeroRowModelTransport

universe uF uV uW

variable {F : Type uF} [Field F] [TopologicalSpace F]
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {V' : Type uW} [AddCommGroup V'] [Module ℂ V']

/-- Transport a representation along an equality of the rank gaps. -/
private def gapRepresentationCast {d e : ℕ} (h : d = e)
    (π : Representation ℂ (Langlands.GeneralLinear (n + e + 1) F) V) :
    Representation ℂ (Langlands.GeneralLinear (n + d + 1) F) V := by
  cases h
  exact π

/-- Transport its specified Whittaker functional along the same equality. -/
private def gapFunctionalCast {d e : ℕ} (h : d = e)
    (π : Representation ℂ (Langlands.GeneralLinear (n + e + 1) F) V)
    (ℓ : glFunctionals ψ (n + e) π) :
    glFunctionals ψ (n + d) (gapRepresentationCast h π) := by
  cases h
  exact ℓ

private theorem gapRepresentationCast_whittakerType {d e : ℕ} (h : d = e)
    (π : Representation ℂ (Langlands.GeneralLinear (n + e + 1) F) V)
    (hπ : IsOfWhittakerType (n + e) (standardCharacter ψ (n + e)) π) :
    IsOfWhittakerType (n + d) (standardCharacter ψ (n + d))
      (gapRepresentationCast h π) := by
  cases h
  exact hπ

private theorem gapFunctionalCast_ne_zero {d e : ℕ} (h : d = e)
    (π : Representation ℂ (Langlands.GeneralLinear (n + e + 1) F) V)
    (ℓ : glFunctionals ψ (n + e) π) (hℓ : ℓ.val ≠ 0) :
    (gapFunctionalCast ψ h π ℓ).val ≠ 0 := by
  cases h
  exact hℓ

end ZeroRowModelTransport

/-- The same integrability statement for the topology and Borel structure of the
supplied data `T`. -/
theorem padic_rectangular_schwartz_integrable 
    (F : Type*) [Field F] (T : LocalFieldData F) (j t : ℕ) :
    letI := T.topology
    letI := borel F
    ∀ (ν : AdditiveHaarMeasure F)
      (φ : SchwartzBruhat (Matrix (Fin j) (Fin t) F)),
      Integrable (φ : Matrix (Fin j) (Fin t) F → ℂ)
        (rectangularMeasure ν j t) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.sigmaCompactSpace
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  intro ν φ
  exact rectangular_schwartz_integrable ν j t φ

/-- Assembly of all four clauses from the two remaining analytic and
representation-theoretic prerequisites. Compact support, finite expansion and
algebraic normalization are imported proofs, not additional premises. -/
theorem unequalRankAnalytic_of_prerequisites.{uF,uV,uW} 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n j k : ℕ)
    (hzero : UnequalRankZeroRowAnalyticStatement.{uF,uV,uW} F T n (j + k))
    (hunit : UnequalRankUnitSpanStatement.{uF,uV,uW} F T n j k) :
    UnequalRankAnalyticStatement.{uF,uV,uW} F T n j k := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := T.secondCountableTopology
  let := T.sigmaCompactSpace
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (GeneralLinear.upperUnipotent (n + 1) F)
  let : BorelSpace (GeneralLinear.upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  intro ψ _ μ hμ ν V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ'
  let hgap : 0 + (j + k) + 1 = j + k + 1 := by omega
  let π₀ := gapRepresentationCast hgap π
  let ℓ₀ := gapFunctionalCast ψ hgap π ℓ
  obtain ⟨hc₀, hr₀, hd₀⟩ :=
    hzero ψ μ hμ ν V W π₀ σ
      (gapRepresentationCast_whittakerType ψ hgap π hπ) hσ ℓ₀ ℓ'
      (gapFunctionalCast_ne_zero ψ hgap π ℓ hℓ) hℓ'
  obtain ⟨values, hc, hr, hd⟩ :=
    diagonal_analytic_of_zero_row ψ (normalizedAbsoluteValue T)
      j k T.residueCardinality μ ν π σ ℓ ℓ' hc₀ hr₀ hd₀
  have hexp : ∀ f : (coefficientModel π ℓ).toSubmodule,
      ∃ (m : ℕ)
        (φ : Fin m → Matrix (Fin j) (Fin (n + 1)) F → ℂ)
        (fs : Fin m → (coefficientModel π ℓ).toSubmodule),
        (∀ i, Integrable (φ i) (rectangularMeasure ν j (n + 1))) ∧
        ∀ (g : Langlands.GeneralLinear (n + 1) F) x,
          f.val.val (unequalRankMatrix j k g x) =
            ∑ i, φ i x * (fs i).val.val (appendIdentity n (j + k + 1) g) := by
    intro f
    obtain ⟨m, φ, fs, he⟩ := unequalRankFiniteExpansion F T n j k
      ψ V π hπ ℓ hℓ f
      (unequalRankCompactSupport.{uF,uV} F T n j k ψ V π hπ ℓ hℓ f)
    exact ⟨m, fun i => (φ i : Matrix (Fin j) (Fin (n + 1)) F → ℂ),
      fs, fun i => padic_rectangular_schwartz_integrable F T j (n + 1) ν (φ i), he⟩
  obtain ⟨hconv, hrat, hden⟩ :=
    analytic_of_finite_expansion ψ (normalizedAbsoluteValue T)
      j k T.residueCardinality T.residueCardinality_gt_one
      μ (rectangularMeasure ν j (n + 1)) π σ ℓ ℓ' hexp hc values hr hd
  exact ⟨hconv, hrat, hden,
    normalizedGeneratorExistence _ hden (hunit ψ μ hμ ν V W π σ hπ hσ ℓ ℓ' hℓ hℓ')⟩

/-- The published unit-span theorem leaves only zero-row analytics as an input
to the complete unequal-rank analytic conclusion. -/
theorem unequalRankAnalytic_of_zero_row.{uF,uV,uW} 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n j k : ℕ)
    (hzero : UnequalRankZeroRowAnalyticStatement.{uF,uV,uW} F T n (j + k)) :
    UnequalRankAnalyticStatement.{uF,uV,uW} F T n j k :=
  unequalRankAnalytic_of_prerequisites F T n j k hzero
    (unequalRankUnitSpan.{uF,uV,uW} F T n j k)

end UnequalRankReduction

/-- JPSS Theorem 2.7(i)-(ii) for every unequal-rank block, with the supplied
topology and measures and independent representation universes. -/
theorem unequalRankAnalytic.{uF,uV,uW} 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n j k : ℕ) :
    UnequalRankAnalyticStatement.{uF,uV,uW} F T n j k :=
  Langlands.AllField.RankinSelberg.UnequalRankReduction.unequalRankAnalytic_of_zero_row.{uF,uV,uW} F T n j k
    (unequalRankZeroRowAnalytic.{uF,uV,uW} F T n (j + k))

end Langlands.AllField.RankinSelberg
