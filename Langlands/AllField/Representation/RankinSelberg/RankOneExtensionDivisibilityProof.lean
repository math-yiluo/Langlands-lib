import Langlands.Representation.RankinSelberg.RankOneExtensionDivisibilityProof
import Langlands.AllField.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.AllField.Representation.RankinSelberg.RankOneExtensionFactorTransport
import Langlands.AllField.Representation.RankinSelberg.RankOneExtensionSpanComparisonProof
import Langlands.AllField.Representation.RankinSelberg.SymmetricLPolynomialExistenceProof
/-!
# Restricted rank-one extension reverse L-divisibility

The closed upper-induction form of JPSS Lemma 5.5, assembled from the
published strict span comparison, actual lower-to-upper factor transport,
full normalized Whittaker type and symmetric polynomial existence.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankContinuedFormsStatement EqualRankFunctionalEquationStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement LowerBlockQuotientDisintegrationStatement LowerBlockQuotientGeometryStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RankOneExtensionCompactSectionStatement RankOneExtensionLDivisibilityStatement RankOneExtensionLowerJacquetFunctionalStatement RankOneExtensionScalarCutoffStatement RankOneExtensionSpanComparisonStatement RankOneWhittakerTypeStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt SymmetricLPolynomialExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement centralSpectralElement centralSpectralElement_det_abs centralSpectralElement_mem_center comap_lowerTriangularQuotientMap_properties continuous_determinantOrder continuous_lowerBlockQuotientDensity continuous_lowerTriangularBlockDensity continuous_ord_units continuous_rankOneExtensionLowerCoefficient continuous_rankOneExtensionUnfoldingFunction continuous_rankOneExtensionUnfoldingFunction_of_continuous determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinantWeight_centralSpectralElement diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankContinuedForms equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankUnitValue exists_rankOneExtensionCellSection finiteFunctionMellin finiteFunctionShellSeries hasEqualRankCompactTest_of_kirillov iUnion_determinantSlice inverseUniformizer_normalizedAbsoluteValue isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt isSmooth_oppositeInducing iwasawaTorusSum lastRowCompactOrbit lowerBlockDensity_unipotent_mul lowerBlockQuotientDensity lowerBlockQuotientDensity_mk lowerBlockQuotientDisintegration lowerBlockQuotientGeometry lowerBlockQuotient_eq_smul_map_chart lowerTriangularBlockDensity lowerTriangularBlockDensity_eq_coe lowerTriangularQuotientMap_comap_of_isCompatible lowerTriangularQuotientMap_measurableEmbedding lowerTriangularQuotientMap_mul lowerTriangularRightHaar lowerTriangularRightHaar_properties map_lowerTriangularBlockDensity_mulRight map_rectangularMeasure_mulRight measurableSet_determinantSlice measurable_lowerBlockQuotientDensity measurePreserving_lowerBlockWeightedProduct_diagonal measurePreserving_lowerBlockWeightedProduct_mulRight measurePreserving_lowerBlockWeightedProduct_shear mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType oneVariableMellin padic_quotient_sigmaFinite padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice quotientHaarExistence quotientIwasawaIntegration quotientRootIntegration rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneExtensionCompactSection rankOneExtensionDisintegration_of_statement rankOneExtensionLDivisibility rankOneExtensionLDivisibility_of_certificates_and_span rankOneExtensionLDivisibility_of_inputs rankOneExtensionLowerFamily rankOneExtensionLowerFamily_isSmooth rankOneExtensionLowerInduced rankOneExtensionLowerInducing_isSmooth rankOneExtensionLowerJacquetFunctional rankOneExtensionLowerModel rankOneExtensionLowerSection rankOneExtensionLowerSectionCoefficient rankOneExtensionLowerSectionCoefficient_lowerBlock_mul rankOneExtensionLowerSectionCoefficient_unipotentBlock_mul rankOneExtensionLowerSectionCoefficient_unipotent_mul rankOneExtensionLowerSectionEval rankOneExtensionLowerShape_leviModulus rankOneExtensionLowerToUpper rankOneExtensionLowerToUpperEquiv rankOneExtensionLowerTranslate rankOneExtensionScalarCutoff rankOneExtensionSpanComparison rankOneExtensionSpanComparison_of_pointwise rankOneExtensionSpanComparison_of_statements rankOneExtensionSpanComparison_pointwise rankOneExtensionStableIntegrand rankOneExtensionStableIntegrandMap rankOneExtensionStableIntegrandMap_apply rankOneExtensionStableIntegrand_apply rankOneExtensionStableIntegrand_translate rankOneExtensionStableIntegrand_unipotent_mul rankOneExtensionSymmetricLPolynomial_iff rankOneExtensionTensorContraction_comp_unipotent rankOneExtensionUnfoldingFunction_lowerBlock_mul_upperCell rankOneExtensionUpper_whittakerType_of_normalizedProduct rankOneExtensionWhittakerContraction rankOneExtension_certificates_of_inputs rankOneWhittakerType rectangularMeasure_compactOpen_pos_lt_top rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable symmetricLPolynomialExists unequalRankAnalytic unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIwasawaSupport unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRectangularHaarScaling padicRowFourierEquivariance padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicUnitTestStatement UnipotentOrbitStatement compactLocalization exists_compactOpen_glCoefficientRightStabilizer functionalsCongr inducedLocalization_of_prerequisites mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport unipotentOrbit
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding continuous_lowerBlockCellParameters exists_compactOpenSubgroup_subset_upperUnipotent_mul_lowerTriangular isOpenEmbedding_lowerBlockQuotientChart isOpenEmbedding_lowerTriangularQuotientMap isOpenMap_lowerBlockQuotientChart isOpenMap_lowerBlockQuotientChart_comp_cellParameters isOpen_upperUnipotent_mul_lowerTriangular_inter lowerBlockQuotientChart_range_compl_null measurable_lowerBlockQuotientChart padic_exists_ne_zero_mem_nhds_zero padic_lowerTriangular_leftQuotient_conull padic_setOf_not_upperUnipotent_mul_lowerTriangular upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

private abbrev extensionPredecessors (t : ℕ) : Fin 2 → ℕ := ![0, t]

private theorem extensionRankSum (t : ℕ) :
    ∑ i, (extensionPredecessors t i + 1) = (1 + t) + 1 := by
  simp only [extensionPredecessors, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

private def extensionFamily
    {F : Type uF} [Field F]
    {t : ℕ} {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (χ : Representation ℂ (Langlands.GeneralLinear 1 F) (ULift.{uW} ℂ))
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W)
    (i : Fin 2) :
    Representation ℂ
      (Langlands.GeneralLinear (extensionPredecessors t i + 1) F)
      (Shahidi.pairCarrier (ULift.{uW} ℂ) W i) :=
  match i with
  | 0 => χ
  | 1 => σ

/-- Conditional preservation specialized to the exact upper block family.
The dependent-data transport follows the published two-block assembly pattern;
no multiplicativity assertion is used. -/
theorem rankOneExtensionUpper_whittakerType_of_normalizedProduct
    (htype : NormalizedProductWhittakerTypeStatement.{uF, uW})
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (t : ℕ) {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (χ : Representation ℂ (Langlands.GeneralLinear 1 F) (ULift.{uW} ℂ))
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W)
    (hχ : IsOfWhittakerType 0 (standardCharacter ψ 0) χ)
    (hσ : IsOfWhittakerType t (standardCharacter ψ t) σ) :
    IsOfWhittakerType (1 + t) (standardCharacter ψ (1 + t))
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced (rankOneExtensionUpperShape t)
        (Shahidi.pairFamily χ σ)) := by
  have hblocks :
      ∀ i, IsOfWhittakerType (extensionPredecessors t i)
        (standardCharacter ψ (extensionPredecessors t i)) (extensionFamily χ σ i) := by
    intro i
    fin_cases i
    · exact hχ
    · exact hσ
  have hresult := htype F ψ (1 + t) 2 (extensionPredecessors t)
    (extensionRankSum t) (extensionFamily χ σ) hblocks
  let D := Σ s : {s : Fin 2 → ℕ // (∀ i, 0 < s i) ∧ ∑ i, s i = (1 + t) + 1},
    ∀ i, Representation ℂ (Langlands.GeneralLinear (s.val i) F)
      (Shahidi.pairCarrier (ULift.{uW} ℂ) W i)
  let d₀ : D := ⟨⟨fun i => extensionPredecessors t i + 1,
    ⟨fun i => Nat.succ_pos _, extensionRankSum t⟩⟩, extensionFamily χ σ⟩
  let d₁ : D := ⟨⟨![1, t + 1], ⟨by intro i; fin_cases i <;> exact Nat.succ_pos _,
    by simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]; omega⟩⟩,
    Shahidi.pairFamily χ σ⟩
  have hd : d₀ = d₁ := by
    apply Sigma.ext
    · apply Subtype.ext
      funext i
      fin_cases i <;> rfl
    · apply Function.hfunext rfl
      intro i j hij
      have hij' : i = j := eq_of_heq hij
      subst j
      fin_cases i <;> rfl
  let property : D → Prop := fun d =>
    IsOfWhittakerType (1 + t) (standardCharacter ψ (1 + t))
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced
        ⟨2, d.1.val, d.1.property.1, d.1.property.2⟩ d.2)
  change property d₁
  have hresult' : property d₀ := hresult
  exact hd ▸ hresult'

/-- Construct the actual two certificates conditionally on the separately
owned full-type and common-existence statements at the needed universes. -/
theorem rankOneExtension_certificates_of_inputs
    (htype : NormalizedProductWhittakerTypeStatement.{uF, uW})
    (hexistsBase : SymmetricLPolynomialExistenceStatement.{uF, uV, uW})
    (hexistsInd : SymmetricLPolynomialExistenceStatement.{uF, uV, max uF uW})
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (r t : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W)
    (χ : Quasicharacter F)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType t (standardCharacter ψ t) σ) :
    let χlift : Representation ℂ (Langlands.GeneralLinear 1 F)
        (ULift.{uW} ℂ) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp
        (rankOneCharacter (χ : Fˣ →* ℂˣ))
    ∃ Pbase Pind : ℂ[X],
      IsPadicSymmetricLPolynomial F ψ ν.val π σ Pbase ∧
      IsPadicSymmetricLPolynomial F ψ ν.val π
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced (rankOneExtensionUpperShape t)
          (Shahidi.pairFamily χlift σ)) Pind := by
  let χlift : Representation ℂ (Langlands.GeneralLinear 1 F)
      (ULift.{uW} ℂ) :=
    (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp
      (rankOneCharacter (χ : Fˣ →* ℂˣ))
  have hχ : IsOfWhittakerType 0 (standardCharacter ψ 0) χlift :=
    rankOneExtensionCharacter_isOfWhittakerType F ψ χ
  have hind := rankOneExtensionUpper_whittakerType_of_normalizedProduct
    htype F ψ t χlift σ hχ hσ
  obtain ⟨Pbase, hbase⟩ := hexistsBase F ψ ν r t V W π σ hπ hσ
  obtain ⟨Pind, hind⟩ := hexistsInd F ψ ν r (1 + t) V _
    π ((⟨⟩ : LocalFieldData F).normalizedProductInduced (rankOneExtensionUpperShape t)
      (Shahidi.pairFamily χlift σ)) hπ hind
  exact ⟨Pbase, Pind, hbase, hind⟩

/-- The algebraic assembly, conditional on the actual certificates and the
strict base-to-lower-induced span comparison. -/
theorem rankOneExtensionLDivisibility_of_certificates_and_span
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (r t : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W)
    (χ : Representation ℂ (Langlands.GeneralLinear 1 F) (ULift.{uW} ℂ))
    (hχ : IsSmooth χ)
    (hσ : IsSmooth σ)
    (hrt : t + 3 ≤ r + 1)
    (Pbase Pind : ℂ[X])
    (hbase : IsPadicSymmetricLPolynomial F ψ ν.val π σ Pbase)
    (hind : IsPadicSymmetricLPolynomial F ψ ν.val π
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced (rankOneExtensionUpperShape t)
        (Shahidi.pairFamily χ σ)) Pind) :
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (t + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear (t + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (t + 1) F)
    letI : BorelSpace (upperUnipotent (t + 1) F) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient t F)
    letI : BorelSpace (LeftUnipotentQuotient t F) := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear ((1 + t) + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear ((1 + t) + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent ((1 + t) + 1) F)
    letI : BorelSpace (upperUnipotent ((1 + t) + 1) F) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient (1 + t) F)
    letI : BorelSpace (LeftUnipotentQuotient (1 + t) F) := ⟨rfl⟩
    (∀ [Measure.IsMulRightInvariant (unipotentHaar F t)]
      [Measure.IsMulRightInvariant (unipotentHaar F (1 + t))]
      (μbase : Measure (LeftUnipotentQuotient t F))
      (μind : Measure (LeftUnipotentQuotient (1 + t) F)),
      IsCompatible (upperUnipotent (t + 1) F)
        (generalLinearHaar F t) (unipotentHaar F t) μbase →
      IsCompatible (upperUnipotent ((1 + t) + 1) F)
        (generalLinearHaar F (1 + t))
        (unipotentHaar F (1 + t)) μind →
      zetaSpan (unequalRankZetaValuesAt (r := r) (n := t)
        1 (r - t - 2) (by omega)
        (⟨⟩ : LocalFieldData F).residueCardinality ψ
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) μbase
        (rectangularMeasure ν.val 1 (t + 1)) π σ) ≤
      zetaSpan (unequalRankZetaValuesAt (r := r) (n := 1 + t)
        0 (r - t - 2) (by omega)
        (⟨⟩ : LocalFieldData F).residueCardinality ψ
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) μind
        (rectangularMeasure ν.val 0 ((1 + t) + 1))
        π (rankOneExtensionLowerInduced F t χ σ))) →
      Pbase ∣ Pind := by
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (t + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (t + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (t + 1) F)
  let : BorelSpace (upperUnipotent (t + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient t F)
  let : BorelSpace (LeftUnipotentQuotient t F) := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear ((1 + t) + 1) F)
  let : BorelSpace (Langlands.GeneralLinear ((1 + t) + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent ((1 + t) + 1) F)
  let : BorelSpace (upperUnipotent ((1 + t) + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient (1 + t) F)
  let : BorelSpace (LeftUnipotentQuotient (1 + t) F) := ⟨rfl⟩
  intro hspan
  have hlower : IsPadicSymmetricLPolynomial F ψ ν.val π
      (rankOneExtensionLowerInduced F t χ σ) Pind :=
    (rankOneExtensionSymmetricLPolynomial_iff F t χ σ hχ hσ ψ ν.val π Pind).2 hind
  have hbase' := (isPadicSymmetricLPolynomial_of_le (show t ≤ r by omega)).1 hbase
  have hlower' := (isPadicSymmetricLPolynomial_of_le (show 1 + t ≤ r by omega)).1 hlower
  obtain ⟨⟨hriBase, μbase, hμbase⟩, hgenBase⟩ := hbase'
  obtain ⟨⟨hriInd, μind, hμind⟩, hgenInd⟩ := hlower'
  let := hriBase
  let := hriInd
  have hB := (isPairLPolynomial_of_lt (show t < r by omega)).1
    (hgenBase μbase hμbase) 1 (r - t - 2) (by omega)
  have hI := (isPairLPolynomial_of_lt (show 1 + t < r by omega)).1
    (hgenInd μind hμind) 0 (r - t - 2) (by omega)
  exact (normalizedGeneratorSpanDivisibility _ _ Pbase Pind hB hI).1
    (hspan μbase μind hμbase hμind)

/-- Assemble the exact parent proposition from full type, common existence
at both carrier universes, and the strict span comparison. -/
theorem rankOneExtensionLDivisibility_of_inputs
    (htype : NormalizedProductWhittakerTypeStatement.{uF, uW})
    (hexistsBase : SymmetricLPolynomialExistenceStatement.{uF, uV, uW})
    (hexistsInd : SymmetricLPolynomialExistenceStatement.{uF, uV, max uF uW})
    (hspan : RankOneExtensionSpanComparisonStatement.{uF, uV, uW}) :
    RankOneExtensionLDivisibilityStatement.{uF, uV, uW} := by
  intro F _ _ _ _ ψ ν r t V _ _ W _ _ π σ χ hrt hπ hσ
  let χlift : Representation ℂ (Langlands.GeneralLinear 1 F)
      (ULift.{uW} ℂ) := rankOneExtensionCharacter F χ
  obtain ⟨Pbase, Pind, hbase, hind⟩ :=
    rankOneExtension_certificates_of_inputs htype hexistsBase hexistsInd
      F ψ ν r t π σ χ hπ hσ
  refine ⟨Pbase, Pind, hbase, hind, ?_⟩
  apply rankOneExtensionLDivisibility_of_certificates_and_span F ψ ν r t π σ χlift
    (rankOneExtensionCharacter_isSmooth F ψ χ) hσ.1.1 hrt Pbase Pind hbase hind
  exact hspan F ψ ν r t π σ χ hrt hπ hσ

/-- JPSS Lemma 5.5 in its original strict rank range, for the actual ordered
upper normalized induction `(χlift, σ₁)`. Both certified polynomials and
the reverse divisibility are conclusions. -/
theorem rankOneExtensionLDivisibility :
    RankOneExtensionLDivisibilityStatement.{uF, uV, uW} :=
  rankOneExtensionLDivisibility_of_inputs
    normalizedProductWhittakerType.{uF, uW}
    symmetricLPolynomialExists.{uF, uV, uW}
    symmetricLPolynomialExists.{uF, uV, max uF uW}
    rankOneExtensionSpanComparison.{uF, uV, uW}

end Langlands.AllField.RankinSelberg
