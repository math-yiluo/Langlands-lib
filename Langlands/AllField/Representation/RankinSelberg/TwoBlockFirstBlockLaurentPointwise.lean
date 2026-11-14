import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentPointwise
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentCoefficients
/-!
# The first-block Laurent identity at a representative

At a representative `g` where the iterated upper fiber integrals converge absolutely, the
reflected dual normalized generator applied to the lower coefficients equals the epsilon
monomial times the normalized generator applied to the upper coefficients. Both sides are
row integrals over the last rectangle row `x`; for each `x` the published small functional
equation of the translate by `R(0; x) g` and the first-block coefficient function of `f(g)`
supplies the identity of coefficient functions.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent
open Langlands.RankinSelberg.TwoBlockFirstBlockLaurent hiding dualIntegrand_integrableOn_slice dualIntegrand_reflectionQuotient dualSmallIntegral_series firstBlockCoefficient firstBlockCoefficient_apply firstBlockCoefficient_lowerRadical_mul integrable_rowRestriction inv_leviHalfModulus_blockPair_one lowerIntegrand_firstBlockFiberPoint lower_coefficient_eq_rowIntegral lower_slice_scalar measurePreserving_reflectionQuotient partialSection_firstBlockEmbedding_mul pointwise_laurent_identity reflectionQuotient_mem_determinantSlice scalarSection_firstBlockEmbedding_mul scalarSection_lowerRadical_mul setIntegral_determinantSlice_reflectionQuotient smallIntegral_series smallIntegrand_integrableOn_slice tensorContraction_blockTensor_blockPair_one unequalRankIntegrandAt unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankSliceCoefficient unequalRankSliceCoefficientAt unequalRank_sliceExpansion upperIntegrand_fiberPoint_rowSnoc upper_coefficient_eq_rowIntegral whittaker_blockRotation_firstBlockEmbedding_lowerRadical
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankNormalizedCompactIntegrationStatement EqualRankSliceExpansionStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion finiteFunctionMellin finiteFunctionShellSeries hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow oneVariableMellin pairwise_disjoint_determinantSlice quotientIwasawaIntegration quotientRootIntegration rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice unequalRankAnalytic unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIwasawaSupport unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockFirstBlockQuotient hiding MixedQuotient NormOneRightInvariant blockUnipotent_le_mixedSubgroup continuous_determinantOrder continuous_fiberPoint determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinant_mixedEmbedding fiberIntegral fiberIntegral_def fiberIntegral_mixedEmbedding_mul fiberIntegral_mixedSubgroup_mul fiberPoint_mem_determinantSlice_iff fiberPoint_mixedEmbedding_mul firstBlockAverage firstBlockAverage_mk isClopen_determinantSlice isClosed_mixedSubgroup measurableSet_determinantSlice mem_determinantSlice mem_mixedSubgroup_iff mem_mixedSubgroup_iff_determinantNorm mem_normOneSubgroup_iff mem_normOneSubgroup_iff_normalizedAbs mixedCoordinates mixedCoordinates_mixedEmbedding mixedEmbedding mixedEmbedding_apply mixedEmbedding_index_one_one mixedEmbedding_index_one_zero mixedEmbedding_index_zero_one mixedEmbedding_index_zero_zero mixedEmbedding_mem mixedEmbedding_mixedCoordinates mixedSubgroup mixedSubgroupEquiv mixedSubgroupEquiv_apply_val mixedSubgroupHomeomorph mixedSubgroup_le_normOneSubgroup mixedSubgroup_le_parabolic mk_mem_determinantSlice normOneRightInvariant_of_isCompatible normOneSubgroup ord_determinant_eq_zero rightTranslate_mem_determinantSlice
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding LowerMixedQuotient continuous_determinantOrder continuous_firstBlockFiberPoint continuous_projectionFromLower continuous_projectionFromMixed continuous_radicalFiberPoint determinantOrder determinantOrder_mk determinantOrder_projectionFromLower determinantOrder_projectionFromMixed determinantOrder_radicalFiberPoint determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice firstBlockAverage firstBlockAverage_mk firstBlockEmbedding_mul_lowerRadical_mul_mixedEmbedding firstBlockFiberIntegral firstBlockFiberIntegral_def firstBlockFiberIntegral_lowerMixedSubgroup_mul firstBlockFiberIntegral_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint firstBlockFiberPoint_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint_mk iUnion_determinantSlice integral_comp_radicalChange isClopen_determinantSlice isClosed_lowerMixedSubgroup lowerBlockUnipotent_le_lowerMixedSubgroup lowerMixedCoordinates lowerMixedCoordinates_lowerProduct lowerMixedDiagonal lowerMixedDiagonal_fst_val lowerMixedDiagonal_lowerProduct lowerMixedDiagonal_snd_val lowerMixedSubgroup lowerMixedSubgroupEquiv lowerMixedSubgroupEquiv_apply_val lowerMixedSubgroupEquiv_mul lowerMixedSubgroupEquiv_symm_apply_fst lowerMixedSubgroupHomeomorph lowerMixedSubgroup_le_normOneSubgroup lowerMixedSubgroup_le_oppositeParabolic lowerMixed_decomposition lowerProduct_lowerMixedCoordinates lowerProduct_mem lowerRadical_mul_leviEmbedding_one_mem measurableSet_determinantSlice measurePreserving_radicalChange mem_determinantSlice mem_lowerMixedSubgroup_iff mixedSubgroup_le_lowerMixedSubgroup mk_mem_determinantSlice pairwise_disjoint_determinantSlice projectionFromLower projectionFromLower_mk projectionFromLower_preimage_determinantSlice projectionFromMixed projectionFromMixed_mk projectionFromMixed_preimage_determinantSlice radicalAverage radicalAverage_mk radicalChange radicalChangeHomeomorph radicalChangeHomeomorph_apply radicalChange_apply radicalFiberIntegral radicalFiberIntegral_def radicalFiberIntegral_lowerMixedSubgroup_mul radicalFiberIntegral_lowerRadical_mixedEmbedding_mul radicalFiberPoint radicalFiberPoint_def radicalFiberPoint_lowerRadical_mixedEmbedding_mul radicalFiberPoint_mem_determinantSlice_iff rightTranslate_mem_determinantSlice
open Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicScalarHaarScaling padicUnipotentHaar_iota_fourier_duality_right
open Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis.TwoBlockRowPartialFourier
open Langlands.QuotientIntegration
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest modelKirillovTransfer mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open scoped ENNReal

universe uF uV uW

variable {F : Type uF} [Field F]
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F}

/-- The coefficientwise first-block identity at a representative. -/
theorem pointwise_laurent_identity (hlt : m 0 < t) (hr : t = m 0 + (m 1 + 0 + 1))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (t + 1) F) V)
    (lambda : glFunctionals ψ t π)
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ)
    (Wtest : (coefficientModel π lambda).toSubmodule)
    (Φ : SchwartzBruhat (Fin (t + 1) → F))
    (Kf : (Fin (m 0 + 1) → F) → LeftUnipotentQuotient (m 0) F → ℂ) :
    let T := (⟨⟩ : LocalFieldData F)
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.generalLinearTopologicalGroup (m 0 + 1)
    letI : MeasurableSpace F := borel F
    letI : BorelSpace F := ⟨rfl⟩
    letI : MeasurableSpace (GeneralLinear (m 0 + 1) F) := borel _
    letI : BorelSpace (GeneralLinear (m 0 + 1) F) := ⟨rfl⟩
    letI : MeasurableSpace (upperUnipotent (m 0 + 1) F) := borel _
    letI : BorelSpace (upperUnipotent (m 0 + 1) F) := ⟨rfl⟩
    letI : MeasurableSpace (LeftUnipotentQuotient (m 0) F) := borel _
    letI : BorelSpace (LeftUnipotentQuotient (m 0) F) := ⟨rfl⟩
    ∀ (νA : Measure (LeftUnipotentQuotient (m 0) F)) [SigmaFinite νA],
      IsCompatible (upperUnipotent (m 0 + 1) F) (generalLinearHaar F (m 0))
        (unipotentHaar F (m 0)) νA →
      ∀ (ν : AdditiveHaarMeasure F) (ζ cε : ℂˣ) (d : ℤ) (P Pdual : Polynomial ℂ),
      IsOfWhittakerType t (standardCharacter ψ t) π →
      IsOfWhittakerType (m 0) (inverseStandardCharacter ψ (m 0)) (σ 0) →
      lambda.val ≠ 0 → (ell 0).val ≠ 0 →
      IsNormalizedGenerator
        (unequalRankValuesAt (m 1) 0 hr T.residueCardinality ψ (normalizedAbsoluteValue T) νA
          (rectangularMeasure ν (m 1) (m 0 + 1)) π (σ 0) lambda (ell 0)) P →
      IsNormalizedGenerator
        (dualUnequalRankRationalValuesAt hlt (m 1) 0 hr T.residueCardinality ψ
          (normalizedAbsoluteValue T) νA ν π (σ 0) lambda (ell 0)) Pdual →
      (∀ (fs : (coefficientModel π lambda).toSubmodule)
        (ff : (coefficientModel (σ 0) (ell 0)).toSubmodule),
        ∃ R Rdual : RationalFunctions,
          HasRationalContinuation T.residueCardinality
            (unequalRankIntegralAt (m 1) 0 hr ψ (normalizedAbsoluteValue T) νA
              (rectangularMeasure ν (m 1) (m 0 + 1)) fs.val ff.val) R ∧
          HasRationalContinuation T.residueCardinality
            (dualUnequalRankModelIntegralAt hlt (m 1) 0 hr ψ (normalizedAbsoluteValue T) νA ν
              π (σ 0) lambda (ell 0) fs ff) Rdual ∧
          NormalizedFunctionalEquation T.residueCardinality P Pdual ζ cε t d R Rdual) →
      ∀ g : GeneralLinear (t + 1) F,
      (∀ x v, Kf x (Quotient.mk _ v) = ψ.complex (Matrix.vecMul x (v⁻¹).val 0)) →
      (∀ x q, ‖Kf x q‖ ≤ 1) →
      (∀ k : ℤ, AEStronglyMeasurable (Function.uncurry Kf)
        ((rowMeasure ν (m 0 + 1)).prod (νA.restrict (determinantSlice T (m 0) k)))) →
      (∀ k : ℤ, AEStronglyMeasurable
        (Function.uncurry fun Z q =>
          Langlands.AllField.RankinSelberg.TwoBlockUnfolding.integrand ell f Wtest.val Φ
            (fiberPoint h F q (lowerRadical h F Z * g)))
        ((rectangularMeasure ν (m 1 + 1) (m 0 + 1)).prod
          (νA.restrict (determinantSlice T (m 0) k)))) →
      (∀ k : ℤ, (∫⁻ Z, ∫⁻ q, ‖Langlands.AllField.RankinSelberg.TwoBlockUnfolding.integrand ell f Wtest.val Φ
            (fiberPoint h F q (lowerRadical h F Z * g))‖ₑ
          ∂νA.restrict (determinantSlice T (m 0) k)
          ∂rectangularMeasure ν (m 1 + 1) (m 0 + 1)) ≠ ⊤) →
      let SL : BilateralLaurentSeries := fun k =>
        (T.residueCardinality : ℂ) ^ (-(k * ((m 1 + 1 : ℕ) : ℤ))) *
          ∫ q in determinantSlice T (m 0) k,
            Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.integrand ell f Wtest.val Φ ν
              (firstBlockFiberPoint F h q g) ∂νA
      let SU : BilateralLaurentSeries := fun k =>
        ∫ Z, ∫ q, Langlands.AllField.RankinSelberg.TwoBlockUnfolding.integrand ell f Wtest.val Φ
            (fiberPoint h F q (lowerRadical h F Z * g))
            ∂νA.restrict (determinantSlice T (m 0) k)
            ∂rectangularMeasure ν (m 1 + 1) (m 0 + 1)
      reflectedPolynomial T.residueCardinality Pdual • SL =
        (LaurentPolynomial.C ((ζ : ℂ) ^ t * (cε : ℂ)) * LaurentPolynomial.T d *
            P.toLaurent) • SU := by
  intro T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (m 0 + 1)
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear (m 0 + 1) F) := borel _
  let : BorelSpace (GeneralLinear (m 0 + 1) F) := ⟨rfl⟩
  let : MeasurableSpace (upperUnipotent (m 0 + 1) F) := borel _
  let : BorelSpace (upperUnipotent (m 0 + 1) F) := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient (m 0) F) := borel _
  let : BorelSpace (LeftUnipotentQuotient (m 0) F) := ⟨rfl⟩
  intro νA _ hνA ν ζ cε d P Pdual hπ hσ hlam hell hP hPd hpairs g hKf hKle hKm hH hfin SL SU
  have := Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  have hr' : t = m 0 + (0 + m 1 + 1) := by omega
  let Q : LaurentPolynomial ℂ := LaurentPolynomial.C ((ζ : ℂ) ^ t * (cε : ℂ)) *
    LaurentPolynomial.T d * P.toLaurent
  let a : (coefficientModel π lambda).toSubmodule →
      (coefficientModel (σ 0) (ell 0)).toSubmodule → BilateralLaurentSeries :=
    fun fs ff n => unequalRankSliceCoefficientAt F (m 1) 0 hr ψ νA
      (rectangularMeasure ν (m 1) (m 0 + 1)) fs.val ff.val n
  let a' : (coefficientModel π lambda).toSubmodule →
      (coefficientModel (σ 0) (ell 0)).toSubmodule → BilateralLaurentSeries :=
    fun fs ff n => unequalRankSliceCoefficientAt F 0 (m 1) hr' (ψ.scale (-1)) νA
      (rectangularMeasure ν 0 (m 0 + 1))
      (translateWhittaker (ψ.scale (-1)) t (firstDualFunction ψ t fs.val)
        (blockWeylAt (m 0) t hlt))
      (secondDualFunction ψ (m 0) ff.val) n
  have hFE : ∀ fs ff, reflectedPolynomial T.residueCardinality Pdual •
      reflectSeries T.residueCardinality (a' fs ff) = Q • a fs ff := by
    intro fs ff
    obtain ⟨R, Rd, hR, hRd, hNFE⟩ := hpairs fs ff
    have hRm : R ∈ unequalRankValuesAt (m 1) 0 hr T.residueCardinality ψ
        (normalizedAbsoluteValue T) νA (rectangularMeasure ν (m 1) (m 0 + 1)) π (σ 0)
        lambda (ell 0) := by
      rw [unequalRankValuesAt_eq]
      exact ⟨fs, ff, hR⟩
    have hRdm : Rd ∈ dualUnequalRankRationalValuesAt hlt (m 1) 0 hr T.residueCardinality ψ
        (normalizedAbsoluteValue T) νA ν π (σ 0) lambda (ell 0) := ⟨fs, ff, hRd⟩
    exact smallFE_coefficient_identity T.residueCardinality_gt_one hP hPd hRm hRdm hR hRd hNFE
      (smallIntegral_series F (m 1) 0 hr ψ νA hνA inferInstance ν π (σ 0) hπ hσ lambda
        (ell 0) hlam hell fs ff)
      (dualSmallIntegral_series F hlt (m 1) 0 hr ψ νA hνA inferInstance ν π (σ 0) hπ hσ
        lambda (ell 0) hlam hell fs ff)
  let Φ' : (Fin (m 0 + 1) → F) → ℂ := fun x =>
    Φ (Matrix.vecMul (join (succBlockEquiv h) x (TwoBlockLowerUnfolding.eta (m 1))) g.val)
  let Wx : (Fin (m 0 + 1) → F) → (coefficientModel π lambda).toSubmodule := fun x =>
    modelRepresentation π lambda (lowerRadical h F (rowSnoc 0 x) * g) Wtest
  let Fg := firstBlockCoefficient ell f g
  have hU : ∀ k : ℤ, Integrable (fun x => Φ' x * a (Wx x) Fg k) (rowMeasure ν (m 0 + 1)) ∧
      SU k = ∫ x, Φ' x * a (Wx x) Fg k ∂rowMeasure ν (m 0 + 1) := fun k =>
    upper_coefficient_eq_rowIntegral hr ell f Wtest.val Φ νA ν k g (hH k) (hfin k)
  have hS : ∀ k : ℤ, Integrable (fun x => Φ' x *
        reflectSeries T.residueCardinality (a' (Wx x) Fg) k) (rowMeasure ν (m 0 + 1)) ∧
      SL k = ∫ x, Φ' x * reflectSeries T.residueCardinality (a' (Wx x) Fg) k
        ∂rowMeasure ν (m 0 + 1) := by
    intro k
    let Wg := modelRepresentation π lambda g Wtest
    have hG := dualIntegrand_integrableOn_slice F hlt (m 1) 0 hr ψ νA hνA inferInstance ν π (σ 0)
      hπ hσ lambda (ell 0) hlam hell Wg Fg (-k)
    have hmp := (measurePreserving_reflectionQuotient F (m 0) νA hνA).restrict_preimage
      (measurableSet_determinantSlice T (m 0) (-k))
    have hpre : reflectionQuotient (m 0) ⁻¹' determinantSlice T (m 0) (-k) =
        determinantSlice T (m 0) k := Set.ext fun q => by
      rw [Set.mem_preimage, reflectionQuotient_mem_determinantSlice F (m 0) (-k), neg_neg]
    rw [hpre] at hmp
    have hA := (hmp.integrable_comp_emb (reflectionQuotient (m 0)).measurableEmbedding).mpr hG
    exact lower_coefficient_eq_rowIntegral hlt hr' ell f Wtest.val Φ Kf νA hνA ν k g hKf
      (hKm k) hKle hA
  have eqL : SL = BilateralLaurentSeries.coeffwiseIntegral (rowMeasure ν (m 0 + 1))
      (fun x => Φ' x • reflectSeries T.residueCardinality (a' (Wx x) Fg)) := by
    funext k
    exact (hS k).2
  have eqU : SU = BilateralLaurentSeries.coeffwiseIntegral (rowMeasure ν (m 0 + 1)) (fun x => Φ' x • a (Wx x) Fg) := by
    funext k
    exact (hU k).2
  rw [eqL, eqU]
  refine integral_laurent_identity_ae _ _ (fun n => (hS n).1) (fun n => (hU n).1)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [smul_comm _ (Φ' x), smul_comm Q (Φ' x), hFE]

end Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent
