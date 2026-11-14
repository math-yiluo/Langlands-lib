import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentCoefficients
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentConvergence
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentIntegrands
/-!
# The two large first-block coefficients as row integrals of small coefficients

At a fixed representative `g`, the rectangular average over the lower radical of the upper
first-block average on the slice `k` is the row integral of `Φ((x, η) g)` times the
slice coefficient `k` of the original small integral of the translate by `R(0; x) g`.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent
open Langlands.RankinSelberg.TwoBlockFirstBlockLaurent hiding dualIntegrand_integrableOn_slice dualIntegrand_reflectionQuotient dualSmallIntegral_series firstBlockCoefficient firstBlockCoefficient_apply firstBlockCoefficient_lowerRadical_mul integrable_rowRestriction inv_leviHalfModulus_blockPair_one lowerIntegrand_firstBlockFiberPoint lower_coefficient_eq_rowIntegral lower_slice_scalar measurePreserving_reflectionQuotient partialSection_firstBlockEmbedding_mul reflectionQuotient_mem_determinantSlice scalarSection_firstBlockEmbedding_mul scalarSection_lowerRadical_mul setIntegral_determinantSlice_reflectionQuotient smallIntegral_series smallIntegrand_integrableOn_slice tensorContraction_blockTensor_blockPair_one unequalRankIntegrandAt unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankSliceCoefficient unequalRankSliceCoefficientAt unequalRank_sliceExpansion upperIntegrand_fiberPoint_rowSnoc upper_coefficient_eq_rowIntegral whittaker_blockRotation_firstBlockEmbedding_lowerRadical
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

universe uF uW

variable {F : Type uF} [Field F]
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F}

/-- The upper coefficient at a representative: under absolute convergence of the iterated
fiber integral, it is the row integral of `Φ((x, η) g)` times the original small slice
coefficient of the translate by `R(0; x) g` and the first-block coefficient of `f(g)`. -/
theorem upper_coefficient_eq_rowIntegral (hr : t = m 0 + (m 1 + 0 + 1))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ)
    (Wtest : RankinSelberg.WhittakerFunctions ψ t)
    (Φ : SchwartzBruhat (Fin (t + 1) → F)) :
    let T := (⟨⟩ : LocalFieldData F)
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F := borel F
    letI : BorelSpace F := ⟨rfl⟩
    letI : MeasurableSpace (LeftUnipotentQuotient (m 0) F) := borel _
    letI : BorelSpace (LeftUnipotentQuotient (m 0) F) := ⟨rfl⟩
    ∀ (νA : Measure (LeftUnipotentQuotient (m 0) F)) [SigmaFinite νA]
      (ν : AdditiveHaarMeasure F) (k : ℤ) (g : GeneralLinear (t + 1) F),
      AEStronglyMeasurable
        (Function.uncurry fun Z q =>
          Langlands.AllField.RankinSelberg.TwoBlockUnfolding.integrand ell f Wtest Φ
            (fiberPoint h F q (lowerRadical h F Z * g)))
        ((rectangularMeasure ν (m 1 + 1) (m 0 + 1)).prod
          (νA.restrict (determinantSlice T (m 0) k))) →
      (∫⁻ Z, ∫⁻ q, ‖Langlands.AllField.RankinSelberg.TwoBlockUnfolding.integrand ell f Wtest Φ
            (fiberPoint h F q (lowerRadical h F Z * g))‖ₑ
          ∂νA.restrict (determinantSlice T (m 0) k)
          ∂rectangularMeasure ν (m 1 + 1) (m 0 + 1)) ≠ ⊤ →
      Integrable (fun x => Φ (Matrix.vecMul
            (join (succBlockEquiv h) x (TwoBlockLowerUnfolding.eta (m 1))) g.val) *
          unequalRankSliceCoefficientAt F (m 1) 0 hr ψ νA
            (rectangularMeasure ν (m 1) (m 0 + 1))
            (translateWhittaker ψ t Wtest (lowerRadical h F (rowSnoc 0 x) * g))
            (firstBlockCoefficient ell f g).val k)
        (rowMeasure ν (m 0 + 1)) ∧
      (∫ Z, ∫ q, Langlands.AllField.RankinSelberg.TwoBlockUnfolding.integrand ell f Wtest Φ
            (fiberPoint h F q (lowerRadical h F Z * g))
          ∂νA.restrict (determinantSlice T (m 0) k)
          ∂rectangularMeasure ν (m 1 + 1) (m 0 + 1)) =
        ∫ x, Φ (Matrix.vecMul
            (join (succBlockEquiv h) x (TwoBlockLowerUnfolding.eta (m 1))) g.val) *
          unequalRankSliceCoefficientAt F (m 1) 0 hr ψ νA
            (rectangularMeasure ν (m 1) (m 0 + 1))
            (translateWhittaker ψ t Wtest (lowerRadical h F (rowSnoc 0 x) * g))
            (firstBlockCoefficient ell f g).val k
          ∂rowMeasure ν (m 0 + 1) := by
  subst hr
  intro T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient (m 0) F) := borel _
  let : BorelSpace (LeftUnipotentQuotient (m 0) F) := ⟨rfl⟩
  intro νA _ ν k g hH hfin
  have := Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  obtain ⟨hint, heq⟩ := integral_rectangular_rowSnoc ν
    (νA.restrict (determinantSlice T (m 0) k)) (m 1) (m 0 + 1) _ hH hfin
  have hpt : ∀ x : Fin (m 0 + 1) → F,
      (∫ q, ∫ y, Langlands.AllField.RankinSelberg.TwoBlockUnfolding.integrand ell f Wtest Φ
          (fiberPoint h F q (lowerRadical h F
            (fun i => Fin.snoc (α := fun _ => Fin (m 0 + 1) → F) (fun j => y j) x i) * g))
          ∂rectangularMeasure ν (m 1) (m 0 + 1) ∂νA.restrict (determinantSlice T (m 0) k)) =
        Φ (Matrix.vecMul
            (join (succBlockEquiv h) x (TwoBlockLowerUnfolding.eta (m 1))) g.val) *
          unequalRankSliceCoefficientAt F (m 1) 0 rfl ψ νA
            (rectangularMeasure ν (m 1) (m 0 + 1))
            (translateWhittaker ψ _ Wtest (lowerRadical h F (rowSnoc 0 x) * g))
            (firstBlockCoefficient ell f g).val k := by
    intro x
    have hq : ∀ q : LeftUnipotentQuotient (m 0) F,
        (∫ y, Langlands.AllField.RankinSelberg.TwoBlockUnfolding.integrand ell f Wtest Φ
            (fiberPoint h F q (lowerRadical h F
              (fun i => Fin.snoc (α := fun _ => Fin (m 0 + 1) → F)
                (fun j => y j) x i) * g))
            ∂rectangularMeasure ν (m 1) (m 0 + 1)) =
          (∫ y, unequalRankIntegrand ψ (normalizedAbsoluteValue T) (m 1) 0
              (translateWhittaker ψ _ Wtest (lowerRadical h F (rowSnoc 0 x) * g))
              (firstBlockCoefficient ell f g).val 0 y q
            ∂rectangularMeasure ν (m 1) (m 0 + 1)) *
            Φ (Matrix.vecMul
              (join (succBlockEquiv h) x (TwoBlockLowerUnfolding.eta (m 1))) g.val) := by
      intro q
      induction q using Quotient.inductionOn with
      | h v =>
        rw [← integral_mul_const]
        congr 1
        funext y
        exact upperIntegrand_fiberPoint_rowSnoc h ell f Wtest Φ v y x g
    simp_rw [hq]
    rw [integral_mul_const, mul_comm]
    rfl
  refine ⟨?_, ?_⟩
  · simpa only [hpt] using hint
  · rw [heq]
    simp only [hpt]

/-- The row restriction `x ↦ Φ((x, η) g)` of a Schwartz–Bruhat function is integrable. -/
theorem integrable_rowRestriction
    (ψ' : HarmonicAnalysis.UnitaryAdditiveCharacter F)
    (μ : letI : MeasurableSpace F := borel F
      AdditiveHaarMeasure F)
    (Φ : SchwartzBruhat (Fin (t + 1) → F)) (g : GeneralLinear (t + 1) F) :
    letI : MeasurableSpace F := borel F
    Integrable (fun x => Φ (Matrix.vecMul
        (join (succBlockEquiv h) x (TwoBlockLowerUnfolding.eta (m 1))) g.val))
      (rowMeasure μ (m 0 + 1)) := by
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  have := Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure μ
  have : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
  have : TotallyDisconnectedSpace F := by
    let : NonarchimedeanRing F := by
      convert! ValuativeRel.nonarchimedeanRing F
      exact Valuation.toTopologicalSpace_eq _
    infer_instance
  have hint := rowPartialFourierIntegrand_integrable ψ' μ (succBlockEquiv h) (rowTranslate g Φ)
    0 (TwoBlockLowerUnfolding.eta (m 1))
  simpa only [rowTranslate_apply, rowPairing, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    AddChar.map_zero_eq_one, one_mul] using hint

/-- On the small slice `k`, the lower density `q^(-k b)`, the inverse half modulus and the
Jacobian `|det v|⁻¹` combine to `q^k` times the transformed small determinant weight. -/
theorem lower_slice_scalar (k : ℤ) (v : GeneralLinear (m 0 + 1) F)
    (hv : (Quotient.mk _ v : LeftUnipotentQuotient (m 0) F) ∈
        determinantSlice (⟨⟩ : LocalFieldData F) (m 0) k) :
    ((⟨⟩ : LocalFieldData F).residueCardinality : ℂ) ^ (-(k * ((m 1 + 1 : ℕ) : ℤ))) *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) v
          (-(((m 1 + 1 : ℕ) : ℂ) / 2)) *
        (((⟨⟩ : LocalFieldData F).normalizedAbs (Matrix.det v.val))⁻¹ : ℂ) =
      ((⟨⟩ : LocalFieldData F).residueCardinality : ℂ) ^ k *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) v
          (-(0 - ((0 + m 1 + 1 : ℕ) : ℂ) / 2)) := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  set q := T.residueCardinality with hq_def
  have hq1 : 1 < q := T.residueCardinality_gt_one
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_one.trans hq1).ne'
  have hord : T.ord (Matrix.det v.val) = k := hv
  have habs : T.normalizedAbs (Matrix.det v.val) = (q : ℝ) ^ (-k) :=
    (mk_mem_determinantSlice_iff_normalizedAbs T).mp hv
  rw [normalizedDeterminantWeight_eq_spectralPoint_zpow, normalizedDeterminantWeight_eq_spectralPoint_zpow,
    hord, habs]
  simp only [spectralPoint, neg_neg, zero_sub, Nat.zero_add]
  set X : ℂ := (q : ℂ) ^ ((((m 1 + 1 : ℕ) : ℂ)) / 2) with hX_def
  have hX : X ≠ 0 := by
    rw [hX_def]
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hq0)
  have hXinv : (T.residueCardinality : ℂ) ^ (-((((m 1 + 1 : ℕ) : ℂ)) / 2)) = X⁻¹ := by
    rw [hX_def, Complex.cpow_neg]
  have hX2 : X ^ 2 = (q : ℂ) ^ (m 1 + 1) := by
    rw [hX_def, ← Complex.cpow_nat_mul, ← Complex.cpow_natCast]
    congr 1
    push_cast
    ring
  have hcast : (((q : ℝ) ^ (-k) : ℝ) : ℂ) = (q : ℂ) ^ (-k) := by push_cast; rfl
  have hY : (X ^ k) ^ 2 = (q : ℂ) ^ (k * ((m 1 + 1 : ℕ) : ℤ)) := by
    rw [← zpow_natCast (X ^ k) 2, ← zpow_mul, mul_comm k, zpow_mul, zpow_natCast, hX2,
      ← zpow_natCast (q : ℂ) (m 1 + 1), ← zpow_mul, mul_comm]
  have hXk : X ^ k ≠ 0 := zpow_ne_zero _ hX
  have hqk : (q : ℂ) ^ k ≠ 0 := zpow_ne_zero _ hq0
  rw [hcast, hXinv, inv_zpow, zpow_neg, ← hY, zpow_neg, inv_inv]
  field_simp

/-- The lower coefficient at a representative: the lower density times the first-block
average on the slice `k` is the row integral of `Φ((x, η) g)` times the reflected series
of the transformed small slice coefficients of the translate by `R(0; x) g`. -/
theorem lower_coefficient_eq_rowIntegral (hlt : m 0 < t) (hr : t = m 0 + (0 + m 1 + 1))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ)
    (Wtest : RankinSelberg.WhittakerFunctions ψ t)
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
      ∀ (ν : AdditiveHaarMeasure F) (k : ℤ) (g : GeneralLinear (t + 1) F),
      (∀ x v, Kf x (Quotient.mk _ v) = ψ.complex (Matrix.vecMul x (v⁻¹).val 0)) →
      AEStronglyMeasurable (Function.uncurry Kf)
        ((rowMeasure ν (m 0 + 1)).prod (νA.restrict (determinantSlice T (m 0) k))) →
      (∀ x q, ‖Kf x q‖ ≤ 1) →
      Integrable (fun q => ∫ z, unequalRankIntegrandAt F 0 (m 1) hr (ψ.scale (-1))
            (normalizedAbsoluteValue T)
            (translateWhittaker (ψ.scale (-1)) t
              (firstDualFunction ψ t (translateWhittaker ψ t Wtest g)) (blockWeylAt (m 0) t hlt))
            (secondDualFunction ψ (m 0) (firstBlockCoefficient ell f g).val) 0 z
            (reflectionQuotient (m 0) q)
          ∂rectangularMeasure ν 0 (m 0 + 1)) (νA.restrict (determinantSlice T (m 0) k)) →
      Integrable (fun x => Φ (Matrix.vecMul
            (join (succBlockEquiv h) x (TwoBlockLowerUnfolding.eta (m 1))) g.val) *
          reflectSeries T.residueCardinality (fun n => unequalRankSliceCoefficientAt F 0 (m 1) hr
            (ψ.scale (-1)) νA (rectangularMeasure ν 0 (m 0 + 1))
            (translateWhittaker (ψ.scale (-1)) t (firstDualFunction ψ t
              (translateWhittaker ψ t Wtest (lowerRadical h F (rowSnoc 0 x) * g)))
              (blockWeylAt (m 0) t hlt))
            (secondDualFunction ψ (m 0) (firstBlockCoefficient ell f g).val) n) k)
        (rowMeasure ν (m 0 + 1)) ∧
      (T.residueCardinality : ℂ) ^ (-(k * ((m 1 + 1 : ℕ) : ℤ))) *
          (∫ q in determinantSlice T (m 0) k, Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.integrand ell f Wtest Φ ν
            (firstBlockFiberPoint F h q g) ∂νA) =
        ∫ x, Φ (Matrix.vecMul
            (join (succBlockEquiv h) x (TwoBlockLowerUnfolding.eta (m 1))) g.val) *
          reflectSeries T.residueCardinality (fun n => unequalRankSliceCoefficientAt F 0 (m 1) hr
            (ψ.scale (-1)) νA (rectangularMeasure ν 0 (m 0 + 1))
            (translateWhittaker (ψ.scale (-1)) t (firstDualFunction ψ t
              (translateWhittaker ψ t Wtest (lowerRadical h F (rowSnoc 0 x) * g)))
              (blockWeylAt (m 0) t hlt))
            (secondDualFunction ψ (m 0) (firstBlockCoefficient ell f g).val) n) k
          ∂rowMeasure ν (m 0 + 1) := by
  subst hr
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
  intro νA _ hνA ν k g hKf hKm hKle hA
  have := Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  let Fg := (firstBlockCoefficient ell f g).val
  let Wd : (Fin (m 0 + 1) → F) → _ := fun x =>
    translateWhittaker (ψ.scale (-1)) _ (firstDualFunction ψ _
      (translateWhittaker ψ _ Wtest (lowerRadical h F (rowSnoc 0 x) * g)))
      (blockWeylAt (m 0) _ hlt)
  let A : LeftUnipotentQuotient (m 0) F → ℂ := fun q =>
    ∫ z, unequalRankIntegrand (ψ.scale (-1)) (normalizedAbsoluteValue T) 0 (m 1)
      (translateWhittaker (ψ.scale (-1)) _
        (firstDualFunction ψ _ (translateWhittaker ψ _ Wtest g)) (blockWeylAt (m 0) _ hlt))
      (secondDualFunction ψ (m 0) Fg) 0 z (reflectionQuotient (m 0) q)
      ∂rectangularMeasure ν 0 (m 0 + 1)
  let Φ' : (Fin (m 0 + 1) → F) → ℂ := fun x =>
    Φ (Matrix.vecMul (join (succBlockEquiv h) x (TwoBlockLowerUnfolding.eta (m 1))) g.val)
  have hΦ : Integrable Φ' (rowMeasure ν (m 0 + 1)) := integrable_rowRestriction ψ ν Φ g
  have hfac : ∀ x q, (∫ z, unequalRankIntegrand (ψ.scale (-1)) (normalizedAbsoluteValue T)
      0 (m 1) (Wd x) (secondDualFunction ψ (m 0) Fg) 0 z (reflectionQuotient (m 0) q)
      ∂rectangularMeasure ν 0 (m 0 + 1)) = Kf x q * A q := by
    intro x q
    induction q using Quotient.inductionOn with
    | h v =>
      simp only [A, Wd, rectangularMeasure_zero_rows, integral_dirac]
      rw [dualIntegrand_reflectionQuotient h hlt, dualIntegrand_reflectionQuotient h hlt,
        translateWhittaker_apply, translateWhittaker_apply, mul_assoc (blockRotation h F),
        mul_assoc (blockRotation h F), whittaker_blockRotation_firstBlockEmbedding_lowerRadical,
        hKf]
      ring
  have ha' : ∀ x, unequalRankSliceCoefficientAt F 0 (m 1) rfl (ψ.scale (-1)) νA
      (rectangularMeasure ν 0 (m 0 + 1)) (Wd x) (secondDualFunction ψ (m 0) Fg) (-k) =
      ∫ q in determinantSlice T (m 0) k, Kf x q * A q ∂νA := by
    intro x
    change (∫ q in determinantSlice T (m 0) (-k), ∫ z, unequalRankIntegrand (ψ.scale (-1))
        (normalizedAbsoluteValue T) 0 (m 1) (Wd x) (secondDualFunction ψ (m 0) Fg) 0 z q
        ∂rectangularMeasure ν 0 (m 0 + 1) ∂νA) = _
    rw [setIntegral_determinantSlice_reflectionQuotient F (m 0) (-k) νA hνA, neg_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun q => hfac x q)
  obtain ⟨hint3, heq3⟩ := integral_mul_integral_swap (νA.restrict (determinantSlice T (m 0) k))
    (rowMeasure ν (m 0 + 1)) A Φ' Kf hA hΦ hKm hKle
  have hrefl : ∀ x, reflectSeries T.residueCardinality (fun n => unequalRankSliceCoefficientAt F
      0 (m 1) rfl (ψ.scale (-1)) νA (rectangularMeasure ν 0 (m 0 + 1)) (Wd x)
      (secondDualFunction ψ (m 0) Fg) n) k =
      (T.residueCardinality : ℂ) ^ k *
        ∫ q in determinantSlice T (m 0) k, Kf x q * A q ∂νA := by
    intro x
    change (T.residueCardinality : ℂ) ^ k * unequalRankSliceCoefficientAt F 0 (m 1) rfl
      (ψ.scale (-1)) νA (rectangularMeasure ν 0 (m 0 + 1)) (Wd x)
      (secondDualFunction ψ (m 0) Fg) (-k) = _
    rw [ha' x]
  refine ⟨?_, ?_⟩
  · refine (hint3.const_mul ((T.residueCardinality : ℂ) ^ k)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    change (T.residueCardinality : ℂ) ^ k *
        (Φ' x * ∫ q in determinantSlice T (m 0) k, Kf x q * A q ∂νA) =
      Φ' x * reflectSeries T.residueCardinality _ k
    rw [hrefl x]
    ring
  · have hpt : ∀ q ∈ determinantSlice T (m 0) k,
        (T.residueCardinality : ℂ) ^ (-(k * ((m 1 + 1 : ℕ) : ℤ))) *
            Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.integrand ell f Wtest Φ ν (firstBlockFiberPoint F h q g) =
          (T.residueCardinality : ℂ) ^ k *
            (A q * ∫ x, Kf x q * Φ' x ∂rowMeasure ν (m 0 + 1)) := by
      intro q hq
      induction q using Quotient.inductionOn with
      | h v =>
        have hI : (∫ x, Kf x (Quotient.mk _ v) * Φ' x ∂rowMeasure ν (m 0 + 1)) =
            ∫ x, ψ.complex (Matrix.vecMul x (v⁻¹).val 0) *
              Φ (Matrix.vecMul (join (succBlockEquiv h) x (TwoBlockLowerUnfolding.eta (m 1))) g.val)
              ∂rowMeasure ν (m 0 + 1) :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => by
            dsimp only [Φ']
            rw [hKf])
        rw [hI, lowerIntegrand_firstBlockFiberPoint ell f Wtest Φ ν v g]
        simp only [A, rectangularMeasure_zero_rows, integral_dirac]
        rw [dualIntegrand_reflectionQuotient h hlt, translateWhittaker_apply,
          mul_assoc (blockRotation h F)]
        linear_combination
          (Wtest.val (blockRotation h F * (firstBlockEmbedding h F v * g)) *
            Fg.val v *
            ∫ x, ψ.complex (Matrix.vecMul x (v⁻¹).val 0) *
              Φ (Matrix.vecMul (join (succBlockEquiv h) x (TwoBlockLowerUnfolding.eta (m 1))) g.val)
              ∂rowMeasure ν (m 0 + 1)) * lower_slice_scalar k v hq
    calc (T.residueCardinality : ℂ) ^ (-(k * ((m 1 + 1 : ℕ) : ℤ))) *
          (∫ q in determinantSlice T (m 0) k, Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.integrand ell f Wtest Φ ν
            (firstBlockFiberPoint F h q g) ∂νA)
        = ∫ q in determinantSlice T (m 0) k,
            (T.residueCardinality : ℂ) ^ (-(k * ((m 1 + 1 : ℕ) : ℤ))) *
              Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.integrand ell f Wtest Φ ν (firstBlockFiberPoint F h q g)
            ∂νA := (integral_const_mul _ _).symm
      _ = ∫ q in determinantSlice T (m 0) k, (T.residueCardinality : ℂ) ^ k *
            (A q * ∫ x, Kf x q * Φ' x ∂rowMeasure ν (m 0 + 1)) ∂νA :=
          setIntegral_congr_fun (measurableSet_determinantSlice T (m 0) k) hpt
      _ = (T.residueCardinality : ℂ) ^ k * ∫ x, Φ' x *
            ∫ q in determinantSlice T (m 0) k, Kf x q * A q ∂νA ∂rowMeasure ν (m 0 + 1) := by
          rw [integral_const_mul, heq3]
      _ = ∫ x, Φ' x * reflectSeries T.residueCardinality (fun n => unequalRankSliceCoefficientAt F
            0 (m 1) rfl (ψ.scale (-1)) νA (rectangularMeasure ν 0 (m 0 + 1)) (Wd x)
            (secondDualFunction ψ (m 0) Fg) n) k ∂rowMeasure ν (m 0 + 1) := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          dsimp only
          rw [hrefl x]
          ring

end Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent
