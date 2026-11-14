import Langlands.Representation.RankinSelberg.TwoBlockLowerFourierAnalytic
import Langlands.AllField.HarmonicAnalysis.TwoBlockRowFourierCompanionProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFourierMeasure
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerUnfoldingIntegrandData
/-! # Fourier specialization and coefficient change of variables -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockLowerFourier
open Langlands.RankinSelberg.TwoBlockLowerFourier hiding lowerDuality_measure_transport lowerDuality_order lowerDuality_slices lowerDuality_symm_order ord_determinant_dual ord_determinant_weylLong partialSection_fourier rowCompanion_contiguous
open Langlands.AllField.RankinSelberg.TwoBlockLowerFourier
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement TwoBlockRowFourierCompanionStatement padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling twoBlockRowFourierCompanion
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerUnfolding hiding groupIntegrand groupIntegrand_def groupIntegrand_lowerBlockUnipotent_mul integrand integrand_mk integrand_mk_eq_groupIntegrand isTopologicalRing_carrier partialSection partialSection_apply partialSection_lowerBlockUnipotent_mul rowMeasure_map_vecMul_upperUnipotent scalarSection_lowerBlockUnipotent_mul sigmaFinite_additiveHaarMeasure whittaker_blockRotation_lowerBlockUnipotent_mul
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding
open Langlands.HarmonicAnalysis.TwoBlockRowPartialFourier

universe uF uX uY

section Rows


end Rows

section DualTest


end DualTest

section Padic

variable (F : Type uF) [Field F]

/-- The published pure row identity, expressed at any equal contiguous total rank. -/
theorem rowCompanion_contiguous [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    let T := (⟨⟩ : LocalFieldData F)
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI : TotallyDisconnectedSpace F := by
      let : NonarchimedeanRing F := by
        convert! ValuativeRel.nonarchimedeanRing F
        exact Valuation.toTopologicalSpace_eq _
      infer_instance
    letI : MeasurableSpace F := borel F
    letI : BorelSpace F := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F)
      (μ : AdditiveHaarMeasure F), IsSelfDual ψ μ →
      ∀ (a b N : ℕ) (hab : a + b = N) (hba : b + a = N),
        0 < a → 0 < b →
        ∀ (Φ Φhat : SchwartzBruhat (Fin N → F)),
          IsRowFourierPair ψ μ Φ Φhat →
          ∀ (g : GeneralLinear N F)
            (ξ : Fin b → F) (η : Fin a → F),
            (∫ u, ψ.complex (-rowPairing u ξ) *
                Φhat (Matrix.vecMul (join (contiguousEquiv hba) u η)
                  (weylLong N F * inverseTranspose N F g).val)
                ∂rowMeasure μ b) =
              (T.normalizedAbs (determinant g : F) : ℂ) *
                ∫ w, ψ.complex (rowPairing w (η ∘ Fin.rev)) *
                  Φ (Matrix.vecMul (join (contiguousEquiv hab) w (ξ ∘ Fin.rev)) g.val)
                  ∂rowMeasure μ a := by
  intro T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let : TotallyDisconnectedSpace F := by
    let : NonarchimedeanRing F := by
      convert! ValuativeRel.nonarchimedeanRing F
      exact Valuation.toTopologicalSpace_eq _
    infer_instance
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  intro ψ μ hsd a b N hab hba ha hb Φ Φhat hpair g ξ η
  subst N
  have hc := (twoBlockRowFourierCompanion F ψ μ hsd a b ha hb).2 Φ Φhat hpair g ξ η
  have hdet : (T.normalizedAbs (determinant g : F) : ℂ) ≠ 0 := by
    exact_mod_cast (T.normalizedAbs_pos (determinant g).ne_zero).ne'
  have hc' := hc.2.2
  change (T.normalizedAbs (determinant g : F) : ℂ)⁻¹ * _ = _ at hc'
  have heq := congrArg
    (fun z : ℂ => (T.normalizedAbs (determinant g : F) : ℂ) * z) hc'
  have hj (u : Fin b → F) :
      join (contiguousEquiv hba) u η = twoBlockSwappedRow u η := by
    rw [join_contiguousEquiv]
    rfl
  have hj' (w : Fin a → F) :
      join (contiguousEquiv rfl) w (ξ ∘ Fin.rev) = Fin.append w (ξ ∘ Fin.rev) := by
    rw [join_contiguousEquiv]
    rfl
  simpa only [hj, hj', ← mul_assoc, mul_inv_cancel₀ hdet, one_mul] using heq

/-- Specialization at the actual source rows and the actual lower partial sections. -/
theorem partialSection_fourier [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {t : ℕ} {m : Fin 2 → ℕ}
    (h : ∑ i, (m i + 1) = t + 1) :
    let T := (⟨⟩ : LocalFieldData F)
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI : TotallyDisconnectedSpace F := by
      let : NonarchimedeanRing F := by
        convert! ValuativeRel.nonarchimedeanRing F
        exact Valuation.toTopologicalSpace_eq _
      infer_instance
    letI : MeasurableSpace F := borel F
    letI : BorelSpace F := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F)
      (μ : AdditiveHaarMeasure F), IsSelfDual ψ μ →
      ∀ (Φ Φhat : SchwartzBruhat (Fin (t + 1) → F)),
        IsRowFourierPair ψ μ Φ Φhat →
        ∀ g : GeneralLinear (t + 1) F,
          partialSection (reverse_sum h) (ψ.scale (-1)) μ Φhat
              (weylLong (t + 1) F * inverseTranspose (t + 1) F g) =
            (T.normalizedAbs (determinant g : F) : ℂ) *
              partialSection h ψ μ Φ g := by
  intro T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let : TotallyDisconnectedSpace F := by
    let : NonarchimedeanRing F := by
      convert! ValuativeRel.nonarchimedeanRing F
      exact Valuation.toTopologicalSpace_eq _
    infer_instance
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  intro ψ μ hsd Φ Φhat hpair g
  have hc := rowCompanion_contiguous F ψ μ hsd (m 0 + 1) (m 1 + 1) (t + 1)
    (TwoBlockJacquet.blockRanks_add h)
    ((Nat.add_comm _ _).trans (TwoBlockJacquet.blockRanks_add h))
    (Nat.succ_pos _) (Nat.succ_pos _) Φ Φhat hpair g (zeta (m 1)) (eta (m 0))
  have hscale (x : F) : (ψ.scale (-1)).complex x = ψ.complex (-x) := by
    simp [UnitaryAdditiveCharacter.complex_apply, UnitaryAdditiveCharacter.scale_apply]
  simp only [partialSection, rowPartialFourierIntegral, rowTranslate_apply, succBlockEquiv,
    hscale]
  simp only [zeta_comp_rev, eta_comp_rev] at hc
  convert hc using 1
  apply integral_congr_ae
  filter_upwards [] with u
  congr 2

end Padic

section Transport


end Transport

end Langlands.AllField.RankinSelberg.TwoBlockLowerFourier
