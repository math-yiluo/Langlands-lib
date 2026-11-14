import Langlands.Representation.RankinSelberg.TwoBlockLowerFourierMeasure
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFourierGeometry
/-! # Exact compatible-measure preservation for actual lower duality -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockLowerFourier
open Langlands.RankinSelberg.TwoBlockLowerFourier hiding lowerDuality_measure_transport lowerDuality_order lowerDuality_slices lowerDuality_symm_order ord_determinant_dual ord_determinant_weylLong
open Langlands.AllField.RankinSelberg.TwoBlockLowerFourier
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory MeasureTheory.Measure
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open scoped NNReal ENNReal

universe uR uF

section General



end General

section Padic

variable (F : Type uF) [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The exact two measure laws and their restrictions, for every compatible input. -/
theorem lowerDuality_measure_transport [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    let T := (⟨⟩ : LocalFieldData F)
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearTopologicalGroup (t + 1)
    let G := GeneralLinear (t + 1) F
    let N := upperUnipotent (t + 1) F
    let Q := LeftQuotient N
    let HQ := LowerQuotient h F
    let HQD := LowerQuotient (reverse_sum h) F
    letI : MeasurableSpace G := borel G
    letI : BorelSpace G := ⟨rfl⟩
    letI : MeasurableSpace N := borel N
    letI : BorelSpace N := ⟨rfl⟩
    letI : MeasurableSpace Q := borel Q
    letI : BorelSpace Q := ⟨rfl⟩
    letI : MeasurableSpace HQ := borel HQ
    letI : BorelSpace HQ := ⟨rfl⟩
    letI : MeasurableSpace HQD := borel HQD
    letI : BorelSpace HQD := ⟨rfl⟩
    ∀ hN : IsMulRightInvariant (unipotentHaar F t),
      letI := hN
      ∀ ν : Measure Q, IsCompatible N (generalLinearHaar F t)
          (unipotentHaar F t) ν →
        let νL := lowerQuotientMeasure F h ν
        let νD := lowerQuotientMeasure F (reverse_sum h) ν
        MeasurePreserving (lowerDuality F h) νL νD ∧
        MeasurePreserving (lowerDuality F h).symm νD νL ∧
        ∀ k : ℤ,
          Measure.map (lowerDuality F h)
              (νL.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k)) =
            νD.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-k)) ∧
          Measure.map (lowerDuality F h).symm
              (νD.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-k))) =
            νL.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k) := by
  intro T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (t + 1)
  intro G N Q HQ HQD
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : MeasurableSpace N := borel N
  let : BorelSpace N := ⟨rfl⟩
  let : MeasurableSpace Q := borel Q
  let : BorelSpace Q := ⟨rfl⟩
  let : MeasurableSpace HQ := borel HQ
  let : BorelSpace HQ := ⟨rfl⟩
  let : MeasurableSpace HQD := borel HQD
  let : BorelSpace HQD := ⟨rfl⟩
  intro hN
  let := hN
  intro ν hν νL νD
  have : LocallyCompactSpace G := T.generalLinearLocallyCompactSpace (t + 1)
  have hD := lowerDuality_preserves F
    (generalLinearHaar F t) (unipotentHaar F t) h ν hν
  have hDs := lowerDuality_symm_preserves F
    (generalLinearHaar F t) (unipotentHaar F t) h ν hν
  refine ⟨hD, hDs, fun k => ?_⟩
  have hs := lowerDuality_slices F h k
  refine ⟨?_, ?_⟩
  · have hm := (hD.restrict_preimage_emb
      (lowerDuality F h).toMeasurableEquiv.measurableEmbedding
      (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-k))).map_eq
    rwa [hs.2.1] at hm
  · have hm := (hDs.restrict_preimage_emb
      (lowerDuality F h).symm.toMeasurableEquiv.measurableEmbedding
      (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k)).map_eq
    rwa [hs.2.2.2] at hm

end Padic

end Langlands.AllField.RankinSelberg.TwoBlockLowerFourier
