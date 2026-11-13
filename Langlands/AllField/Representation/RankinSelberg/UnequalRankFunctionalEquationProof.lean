import Langlands.Representation.RankinSelberg.UnequalRankFunctionalEquationProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankBlockZeroGammaProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankCommonGeneratorProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankGammaPropagationProof
noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding FiniteFunctionMellinStatement FiniteFunctionShellSeriesStatement IwasawaTorusPartitionStatement IwasawaTorusSumStatement ModelAsymptoticTransferStatement OneVariableMellinStatement QuotientIwasawaIntegrationStatement QuotientRootIntegrationStatement RootCoordinateChangeStatement RootCoordinateFiniteFunctionStatement RootSpectralWeightStatement UnequalRankAdjacentBlockSpanStatement UnequalRankAnalyticStatement UnequalRankBilinearUniquenessStatement UnequalRankBlockZeroContinuedFormsStatement UnequalRankBlockZeroGammaAssemblyInput UnequalRankBlockZeroGammaExistenceStatement UnequalRankCommonGeneratorStatement UnequalRankCompactGenericPairingStatement UnequalRankCompactSupportStatement UnequalRankComplementaryTransferStatement UnequalRankFiniteExpansionStatement UnequalRankFourierSmearingStatement UnequalRankFunctionalEquationStatement UnequalRankGammaPropagationStatement UnequalRankIwasawaSupportStatement UnequalRankMirabolicPairingRigidityStatement UnequalRankMirabolicUnitTestStatement UnequalRankSourceLengthBoundStatement UnequalRankUnitSpanStatement UnequalRankZeroRowAnalyticStatement UnequalRankZeroRowNormalizedCompactIntegrationStatement UnequalRankZeroRowRootExpansionStatement ValuationShellIntegrationStatement continuous_ord_units diagonalConj_map diagonal_abs_bound diagonal_abs_last exists_compactOpen_rectangular_subgroup finiteFunctionMellin finiteFunctionShellSeries iwasawaTorusPartition iwasawaTorusSum modelAsymptoticTransfer normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow oneVariableMellin padic_quotient_sigmaFinite padic_rectangular_laws padic_row_instances quotientIwasawaIntegration quotientRootIntegration rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight singleton_modulus_real unequalRankAdjacentBlockSpan unequalRankAnalytic unequalRankBilinearUniqueness unequalRankBlockZeroContinuedForms unequalRankBlockZeroGammaExistence unequalRankCommonGenerator unequalRankCompactGenericPairing unequalRankCompactSupport unequalRankComplementaryTransfer unequalRankFiniteExpansion unequalRankFiniteExpansion_of_cosetExpansion unequalRankFourierSmearingStatement unequalRankFunctionalEquation unequalRankGammaPropagation unequalRankIwasawaSupport unequalRankMirabolicPairingRigidity unequalRankMirabolicUnitTest unequalRankSourceLengthBound unequalRankUnitSpan unequalRankZeroRowAnalytic unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unequalRank_coefficient_invariant valuationShellIntegration
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicLatticeFourierStatement PadicLatticeGeometryStatement PadicLatticeHaarStatement PadicLatticeSchwartzExpansionStatement PadicRectangularHaarScalingStatement PadicRowFourierCutoffStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement SchwartzBruhatValuationBoundsStatement padicLatticeFourier padicLatticeGeometry padicLatticeHaar padicLatticeSchwartzExpansion padicRectangularHaarScaling padicRectangularHaarScalingStatement padicRowFourierCutoff padicRowFourierSurjectivity padicScalarHaarScaling padicSchwartzBruhat_exists_additiveLattice_invariant padicSelfDualMeasureExists schwartzBruhatValuationBounds
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement CoordinateJacquetKernelStatement IrreducibleCoinvariantFinitenessStatement JPSBoundedDilationRecurrenceStatement JPSCoordinateUnitInvarianceStatement JPSDecompositionStatement JPSDilationAssemblyStatement JPSUniformDilationStatement LeviCuspidalCoinvariantFinitenessStatement MirabolicCompactMinimalityStatement MirabolicFiniteLengthStatement MirabolicFunctionalMultiplicityStatement ModelKirillovTransferStatement MultiplicityOneStatement ParabolicInducedCoinvariantFinitenessStatement SmoothSimpleRootSupportStatement SupercuspidalCoinvariantFinitenessStatement UnipotentOrbitStatement compactLocalization coordinateJacquetKernelStatement functionalsCongr irreducibleCoinvariantFiniteness jpsBoundedDilationRecurrence jpsCoordinateUnitInvariance jpsDecomposition jpsDilationAssembly jpsUniformDilation leviCuspidalCoinvariantFiniteness mirabolicCompactMinimality mirabolicFiniteLength mirabolicFunctionalMultiplicity mirabolicFunctionalMultiplicity_canonical mirabolicFunctionalMultiplicity_of_minimality modelKirillovTransfer parabolicInducedCoinvariantFiniteness smoothSimpleRootSupport supercuspidalCoinvariantFiniteness unipotentOrbit
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding UpperUnipotentCompactContainmentStatement upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

section FixedData

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {n r : ℕ}
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {hnr : n < r} {q : ℕ} {ψ : UnitaryAdditiveCharacter F}
  {abv : AbsoluteValue F ℝ} {μ : Measure (LeftUnipotentQuotient n F)}
  {ν : AdditiveHaarMeasure F}
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {ℓ : glFunctionals ψ r π} {ℓ' : glInverseFunctionals ψ n σ}

/-- One normalization at block zero supplies the same monomial for every block
because the gamma multiplier and normalized generators are common. -/
private theorem unequalRankFunctionalEquationConclusion_of_common_generators
    (hq : 1 < q)
    {G : RationalFunctions}
    (hGamma : UnequalRankGammaEquation hnr q ψ abv μ ν π σ ℓ ℓ' G)
    {P Pdual : Polynomial ℂ}
    (hP : ∀ (j k : ℕ) (hr : r = n + (j + k + 1)),
      IsNormalizedGenerator
        (unequalRankValuesAt j k hr q ψ abv μ (rectangularMeasure ν j (n + 1))
          π σ ℓ ℓ') P)
    (hPdual : ∀ (j k : ℕ) (hr : r = n + (j + k + 1)),
      IsNormalizedGenerator
        (dualUnequalRankRationalValuesAt hnr j k hr q ψ abv μ ν π σ ℓ ℓ') Pdual) :
    UnequalRankFunctionalEquationConclusion hnr q ψ abv μ ν π σ ℓ ℓ' := by
  obtain ⟨ζ, hζ, hBlocks⟩ := hGamma
  have hr0 : r = n + (0 + (r - n - 1) + 1) := by omega
  let S := unequalRankValuesAt 0 (r - n - 1) hr0 q ψ abv μ
    (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ'
  let T := dualUnequalRankRationalValuesAt hnr 0 (r - n - 1) hr0
    q ψ abv μ ν π σ ℓ ℓ'
  have hForward : ∀ R ∈ S,
      ∃ Rdual ∈ T, GammaFunctionalEquation q ζ r G R Rdual := by
    intro R hR
    change R ∈ unequalRankValuesAt 0 (r - n - 1) hr0 q ψ abv μ
      (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ' at hR
    rw [unequalRankValuesAt_eq] at hR
    obtain ⟨f, f', hR⟩ := hR
    obtain ⟨R₀, Rdual, hR₀, hRdual, hEq⟩ := (hBlocks 0 (r - n - 1) hr0).2 f f'
    obtain rfl := hR.unique hq hR₀
    exact ⟨Rdual, ⟨f, f', hRdual⟩, hEq⟩
  have hBackward : ∀ Rdual ∈ T,
      ∃ R ∈ S, GammaFunctionalEquation q ζ r G R Rdual := by
    rintro Rdual ⟨f, f', hRdual⟩
    obtain ⟨R, Rdual₀, hR, hRdual₀, hEq⟩ := (hBlocks 0 (r - n - 1) hr0).2 f f'
    obtain rfl := hRdual.unique hq hRdual₀
    refine ⟨R, ?_, hEq⟩
    change R ∈ unequalRankValuesAt 0 (r - n - 1) hr0 q ψ abv μ
      (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ'
    rw [unequalRankValuesAt_eq]
    exact ⟨f, f', hR⟩
  obtain ⟨c, m, hNorm⟩ := gammaNormalization q hq ζ r G S T P Pdual
    (hP 0 (r - n - 1) hr0) (hPdual 0 (r - n - 1) hr0) hForward hBackward
  refine ⟨ζ, c, m, P, Pdual, hζ, ?_⟩
  intro j k hr
  refine ⟨hP j k hr, hPdual j k hr, ?_⟩
  intro f f'
  obtain ⟨R, Rdual, hR, hRdual, hEq⟩ := (hBlocks j k hr).2 f f'
  exact ⟨R, Rdual, hR, hRdual, hNorm R Rdual hEq⟩

/-- Existing dual-model transport carries one common polynomial for the
inverse-transpose pair to the actual complementary-block dual value families. -/
private theorem dualUnequalRank_commonGenerator_of_inverseTranspose
    {Pdual : Polynomial ℂ}
    (hPdual : ∀ (j k : ℕ) (hr : r = n + (j + k + 1)),
      IsNormalizedGenerator
        (unequalRankValuesAt j k hr q (ψ.scale (-1)) abv μ
          (rectangularMeasure ν j (n + 1))
          (inverseTransposePullback π) (inverseTransposePullback σ)
          (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ')) Pdual) :
    ∀ (j k : ℕ) (hr : r = n + (j + k + 1)),
      IsNormalizedGenerator
        (dualUnequalRankRationalValuesAt hnr j k hr q ψ abv μ ν π σ ℓ ℓ') Pdual := by
  intro j k hr
  rw [dualUnequalRankRationalValuesAt_eq]
  exact hPdual k j (by omega)

end FixedData

section PadicAssembly

/-- The valuation-topology bridge used by the published statements, repeated
locally to elaborate their common self-dual-measure telescope in the proof. -/
private theorem valuative_nonarchimedean {K : Type uF} [Field K]
    [TopologicalSpace K] [ValuativeRel K] [IsValuativeTopology K] :
    NonarchimedeanAddGroup K where
  is_nonarchimedean U hU := by
    obtain ⟨S, hS, hSU⟩ :=
      (IsLinearTopology.hasBasis_open_submodule
        (ValuativeRel.valuation K).integer (M := K)).mem_iff.mp hU
    exact ⟨⟨S.toAddSubgroup, hS⟩, hSU⟩

variable (F : Type uF) [Field F] (T : LocalFieldData F)

/-- JPSS Theorem 2.7(iii) for unequal positive ranks: one epsilon monomial
and one normalized polynomial pair work for every complementary block. -/
theorem unequalRankFunctionalEquation (n r : ℕ) :
    UnequalRankFunctionalEquationStatement.{uF, uV, uW} F T n r := by
  have hCommon := unequalRankCommonGenerator.{uF, uV, uW} F T n r
  have hBlockZero := unequalRankBlockZeroGammaExistence.{uF, uV, uW} F T n r
  have hPropagation := unequalRankGammaPropagation.{uF, uV, uW} F T n r
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F
  let := isUniformAddGroup_of_addCommGroup (G := F)
  let := valuative_nonarchimedean (K := F)
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  intro hnr ψ hInv μ hμ ν hν V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ'
  obtain ⟨P, hP⟩ := hCommon hnr ψ μ hμ ν V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
  have hπdual : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r)
      (inverseTransposePullback π) := by
    simpa only [standardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback ψ π hπ
  have hσdual : IsOfWhittakerType n (inverseStandardCharacter (ψ.scale (-1)) n)
      (inverseTransposePullback σ) := by
    simpa only [inverseStandardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback_inverse ψ σ hσ
  obtain ⟨Pdual, hPdual⟩ := hCommon hnr (ψ.scale (-1)) μ hμ ν V W
    (inverseTransposePullback π) (inverseTransposePullback σ) hπdual hσdual
    (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ')
    (firstDualFunctional_ne_zero ψ π hℓ) (secondDualFunctional_ne_zero ψ σ hℓ')
  obtain ⟨G, _hGne, hGzero⟩ :=
    hBlockZero hnr ψ μ hμ ν hν V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
  have hG := hPropagation hnr ψ μ hμ ν hν V W π σ hπ hσ ℓ ℓ' hℓ hℓ' G hGzero
  exact unequalRankFunctionalEquationConclusion_of_common_generators
    T.residueCardinality_gt_one hG hP
    (dualUnequalRank_commonGenerator_of_inverseTranspose hPdual)

end PadicAssembly

end Langlands.AllField.RankinSelberg
