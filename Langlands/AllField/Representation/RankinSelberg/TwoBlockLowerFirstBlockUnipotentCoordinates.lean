import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockUnipotentCoordinates
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockQuotientUnfolding
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockMeasureTransport
/-!
# Block coordinates of the prescribed lower-unipotent Haar

The prescribed Haar on `H⁻ = C⁻¹ N C` unfolds into the two diagonal unipotent
Haar measures and any supplied rectangular Haar, up to its integral-cube mass.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
open Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding lintegral_lowerHaar lintegral_lowerHaar_eq lintegral_unipotentHaar_blockCoordinates lowerHaar lowerHaar_isHaar lowerHaar_isMulRightInvariant lowerHaar_regular lowerMeasureTransportInstance01 lowerMeasureTransportInstance02 lowerMeasureTransportInstance03 lowerMeasureTransportInstance04 lowerMeasureTransportInstance08 lowerMeasureTransportInstance09 lowerMeasureTransportInstance10 lowerMeasureTransportInstance11 lowerMeasureTransportInstance12 lowerMeasureTransportInstance13 lowerMeasureTransportInstance14 lowerMeasureTransportInstance17 lowerMeasureTransportInstance18 lowerMeasureTransportInstance21 lowerMeasureTransportInstance22 lowerMeasureTransportInstance23 lowerMeasureTransportInstance24 lowerMeasure_isCompatible lowerMeasure_sigmaFinite lowerUnipotentCoordinatesInstance01 lowerUnipotentCoordinatesInstance02 lowerUnipotentCoordinatesInstance03 lowerUnipotentCoordinatesInstance04 lowerUnipotentCoordinatesInstance05 lowerUnipotentCoordinatesInstance06 lowerUnipotentCoordinatesInstance07 lowerUnipotentCoordinatesInstance08 lowerUnipotentCoordinatesInstance09 lowerUnipotentCoordinatesInstance10 lowerUnipotentCoordinatesInstance11 lowerUnipotentCoordinatesInstance12 lowerUnipotentCoordinatesInstance13 lowerUnipotentCoordinatesInstance14 lowerUnipotentCoordinatesInstance15 lowerUnipotentCoordinatesInstance16 lowerUnipotentCoordinatesInstance17 lowerUnipotentCoordinatesInstance19 lowerUnipotentCoordinatesInstance20 lowerUnipotentCoordinatesInstance21 lowerUnipotentCoordinatesInstance22 lowerUnipotentCoordinatesInstance23 lowerUnipotentCoordinatesInstance24 quotientAverage_lower_transport
open Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankLastRowReductionStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankLastRowReduction equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockFirstBlockQuotient hiding MixedQuotient NormOneRightInvariant blockUnipotent_le_mixedSubgroup continuous_determinantOrder continuous_fiberPoint determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinant_mixedEmbedding fiberIntegral fiberIntegral_def fiberIntegral_mixedEmbedding_mul fiberIntegral_mixedSubgroup_mul fiberPoint_mem_determinantSlice_iff fiberPoint_mixedEmbedding_mul firstBlockAverage firstBlockAverage_mk instBorelSpaceGeneralLinearCarrier instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instIsNonarchimedeanLocalFieldCarrier instLocallyCompactSpaceMatrixFinCarrier instLocallyCompactSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instLocallyCompactSpaceSubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceGeneralLinearCarrier instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instSecondCountableTopologyGeneralLinearCarrier instSecondCountableTopologySubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instSecondCountableTopologySubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier isClopen_determinantSlice isClosed_mixedSubgroup isOpenEmbedding_normOneSubtype lintegral_blockHaar map_normOneHaar measurableSet_determinantSlice mem_determinantSlice mem_mixedSubgroup_iff mem_mixedSubgroup_iff_determinantNorm mem_normOneSubgroup_iff mem_normOneSubgroup_iff_normalizedAbs mixedCoordinates mixedCoordinates_mixedEmbedding mixedEmbedding mixedEmbedding_apply mixedEmbedding_index_one_one mixedEmbedding_index_one_zero mixedEmbedding_index_zero_one mixedEmbedding_index_zero_zero mixedEmbedding_mem mixedEmbedding_mixedCoordinates mixedHaar mixedHaar_isHaar mixedHaar_isMulRightInvariant mixedHaar_regular mixedSubgroup mixedSubgroupEquiv mixedSubgroupEquiv_apply_val mixedSubgroupHomeomorph mixedSubgroup_le_normOneSubgroup mixedSubgroup_le_parabolic mixed_compatibleMeasureExists mk_mem_determinantSlice normOneHaar normOneHaar_isHaar normOneHaar_isMulRightInvariant normOneHaar_regular normOneRightInvariant_of_isCompatible normOneSubgroup ord_determinant_eq_zero rightTranslate_mem_determinantSlice small_orbitKernel_comp_zero unfoldingInst1 unfoldingInst10 unfoldingInst11 unfoldingInst12 unfoldingInst13 unfoldingInst14 unfoldingInst15 unfoldingInst2 unfoldingInst20 unfoldingInst21 unfoldingInst23 unfoldingInst24 unfoldingInst3 unfoldingInst4 unfoldingInst8 unfoldingInst9
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open scoped ENNReal

universe uF uR

section Rotation


end Rotation

section Algebra

open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet


end Algebra

section Measure

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance lowerUnipotentCoordinatesInstance04 : T2Space F :=
  (⟨⟩ : LocalFieldData F).fieldT2
local instance lowerUnipotentCoordinatesInstance05 : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance lowerUnipotentCoordinatesInstance06 : MeasurableSpace F := borel _
local instance lowerUnipotentCoordinatesInstance07 : BorelSpace F := ⟨rfl⟩
local instance lowerUnipotentCoordinatesInstance08 (a b : ℕ) :
    LocallyCompactSpace (Matrix (Fin b) (Fin a) F) :=
  inferInstanceAs (LocallyCompactSpace (Fin b → Fin a → F))
local instance lowerUnipotentCoordinatesInstance09 (a b : ℕ) :
    SecondCountableTopology (Matrix (Fin b) (Fin a) F) :=
  inferInstanceAs (SecondCountableTopology (Fin b → Fin a → F))
local instance lowerUnipotentCoordinatesInstance10 (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup n
local instance lowerUnipotentCoordinatesInstance11 (n : ℕ) :
    MeasurableSpace (GeneralLinear n F) := borel _
local instance lowerUnipotentCoordinatesInstance12 (n : ℕ) :
    BorelSpace (GeneralLinear n F) := ⟨rfl⟩
local instance lowerUnipotentCoordinatesInstance13 (n : ℕ) :
    SecondCountableTopology (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology n
local instance lowerUnipotentCoordinatesInstance14 (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace n
local instance lowerUnipotentCoordinatesInstance15 (n : ℕ) :
    MeasurableSpace (upperUnipotent n F) := borel _
local instance lowerUnipotentCoordinatesInstance16 (n : ℕ) :
    BorelSpace (upperUnipotent n F) := ⟨rfl⟩
local instance lowerUnipotentCoordinatesInstance17 (n : ℕ) :
    SecondCountableTopology (upperUnipotent n F) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerUnipotentCoordinatesInstance19 :
    MeasurableSpace (lowerBlockUnipotent h F) := borel _
local instance lowerUnipotentCoordinatesInstance20 :
    BorelSpace (lowerBlockUnipotent h F) := ⟨rfl⟩
local instance lowerUnipotentCoordinatesInstance21 {t' : ℕ} {m' : Fin 2 → ℕ}
    (h' : ∑ i, (m' i + 1) = t' + 1) :
    MeasurableSpace (TwoBlockUnipotentQuotient.blockUnipotent h' F) := borel _
local instance lowerUnipotentCoordinatesInstance22 {t' : ℕ} {m' : Fin 2 → ℕ}
    (h' : ∑ i, (m' i + 1) = t' + 1) :
    BorelSpace (TwoBlockUnipotentQuotient.blockUnipotent h' F) := ⟨rfl⟩
local instance lowerUnipotentCoordinatesInstance23 {t' : ℕ} {m' : Fin 2 → ℕ}
    (h' : ∑ i, (m' i + 1) = t' + 1) :
    SecondCountableTopology (TwoBlockUnipotentQuotient.blockUnipotent h' F) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

local notation "O" => Valuation.integer (ValuativeRel.valuation F)

local instance lowerUnipotentCoordinatesInstance24 {t' : ℕ} {m' : Fin 2 → ℕ}
    (h' : ∑ i, (m' i + 1) = t' + 1) :
    LocallyCompactSpace (TwoBlockUnipotentQuotient.blockUnipotent h' F) :=
  (TwoBlockUnipotentQuotient.isClosed_blockUnipotent h' F).isClosedEmbedding_subtypeVal.locallyCompactSpace

/-- The prescribed lower-unipotent Haar is the inverse-conjugation transport of the
standard full-unipotent Haar. -/
theorem lintegral_lowerHaar_eq (ψ : GeneralLinear (t + 1) F → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ x : lowerBlockUnipotent h F, ψ x.val ∂lowerHaar F h =
      ∫⁻ n : upperUnipotent (t + 1) F,
        ψ ((blockRotation h F)⁻¹ * n.val * blockRotation h F)
          ∂unipotentHaar F t := by
  rw [lowerHaar]
  exact lintegral_map (hψ.comp continuous_subtype_val.measurable)
    (continuous_conjugationEquiv_symm_canonical F h).measurable

/-- The block coordinates `(b, Z) ↦ b u(Z)` of the standard full-unipotent Haar, for any
two-block shape, with the fixed block measure unfolded into the two block Haar measures. -/
theorem lintegral_unipotentHaar_blockCoordinates {m' : Fin 2 → ℕ}
    (h' : ∑ i, (m' i + 1) = t + 1)
    (μR : Measure (Matrix (Fin (m' 0 + 1)) (Fin (m' 1 + 1)) F)) [μR.IsAddHaarMeasure]
    (φ : upperUnipotent (t + 1) F → ℝ≥0∞) (hφ : Measurable φ) :
    μR {Z | ∀ i j, Z i j ∈ O} * ∫⁻ n, φ n ∂unipotentHaar F t =
      ∫⁻ y : upperUnipotent (m' 0 + 1) F, ∫⁻ x : upperUnipotent (m' 1 + 1) F,
        ∫⁻ Z, φ (TwoBlockUnipotentQuotientIntegration.coordinates h'
          (TwoBlockUnipotentQuotient.blockUnipotentEquiv h' F
            ((MeasurableEquiv.piFinTwo _).symm (y, x)), Z)) ∂μR
          ∂unipotentHaar F (m' 1) ∂unipotentHaar F (m' 0) := by
  have hcoord := TwoBlockUnipotentQuotientIntegration.map_coordinates_prod F h'
    (TwoBlockUnipotentQuotient.blockHaar F h')
    (TwoBlockUnipotentQuotientIntegration.blockMeasure_integral F h') μR
  have hcm : Measurable (TwoBlockUnipotentQuotientIntegration.coordinates (K := F) h') :=
    (TwoBlockUnipotentQuotientIntegration.continuous_coordinates h').measurable
  have hprod := hφ.comp hcm
  rw [← smul_eq_mul, ← lintegral_smul_measure, ← hcoord, lintegral_map hφ hcm]
  refine (lintegral_prod _ hprod.aemeasurable).trans ?_
  exact lintegral_blockHaar F h' _ hprod.lintegral_prod_right'

/-- **Block coordinates of `H⁻`.** For every rectangular additive Haar `μR`,
the integral-cube mass of `μR` times the prescribed lower-unipotent Haar integral
equals the iterated integral over `diag(x, y) R(Z)` with `x ∈ N_a`, `y ∈ N_b`. -/
theorem lintegral_lowerHaar
    (μR : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)) [μR.IsAddHaarMeasure]
    (ψ : GeneralLinear (t + 1) F → ℝ≥0∞) (hψ : Measurable ψ) :
    μR {Z | ∀ i j, Z i j ∈ O} *
        ∫⁻ x : lowerBlockUnipotent h F, ψ x.val ∂lowerHaar F h =
      ∫⁻ y : upperUnipotent (m 1 + 1) F, ∫⁻ x : upperUnipotent (m 0 + 1) F,
        ∫⁻ Z, ψ ((succBlockShape m h).leviEmbedding F
            (blockPair (m := m) F (x.val, y.val)) * lowerRadical h F Z)
          ∂μR ∂unipotentHaar F (m 0) ∂unipotentHaar F (m 1) := by
  have hφ : Measurable (fun n : upperUnipotent (t + 1) F =>
      ψ ((blockRotation h F)⁻¹ * n.val * blockRotation h F)) :=
    hψ.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  rw [lintegral_lowerHaar_eq F h ψ hψ]
  refine (lintegral_unipotentHaar_blockCoordinates F (m' := fun i => m i.rev) (reverse_sum h)
    μR _ hφ).trans ?_
  refine lintegral_congr fun y => lintegral_congr fun x => lintegral_congr fun Z => ?_
  rw [TwoBlockUnipotentQuotientIntegration.coordinates_val,
    TwoBlockUnipotentQuotient.blockUnipotentEquiv_apply_val,
    blockRotation_inv_mul_coordinates_mul h F]
  rfl

end Measure

end Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
