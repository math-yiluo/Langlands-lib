import Langlands.Representation.GodementJacquet.SupercuspidalCutoffNonzeroOperator
import Langlands.AllField.Representation.GodementJacquet.RegularMatrixZetaOperator
import Langlands.AllField.Representation.GodementJacquet.SupercuspidalCutoffFourierRegularity
/-! # Nonzero Fourier-regular matrix zeta operators -/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding determinantNorm_eq_one_of_mem_conjugateUnipotent determinantUnitTestToMatrixTest determinantUnitTestToMatrixTest_apply determinantUnitTestToMatrixTest_eq_zero hasCompactSupport_determinantUnit_coefficient oneBlockDeterminantUnitHomeomorph supercuspidalCutoffFourierEvaluation supercuspidalCutoffMatrixTest supercuspidalCutoffMatrixTest_apply supercuspidalCutoffMatrixTest_apply_of_not_mem supercuspidalCutoffMatrixTest_fourier_eq_zero_of_stabilizer supercuspidalCutoffMatrixTest_fourier_right supercuspidalCutoffMatrixTest_fourier_singular supercuspidalCutoffMatrixTest_mem_fourierRegularMatrixTests supercuspidalCutoffMatrixTest_right supercuspidalCutoffMatrixTest_singular supercuspidalDeterminantUnitCoefficient
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding measurePreserving_rectangular_mul_mul padicLatticeGeometry padicRectangularHaarScaling padicScalarHaarScaling rectangularFourierIntegral_comp_mul_mul rectangularFourierIntegral_translate_decomposition rectangularPairing_mul_mul
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFrobeniusStatement EqualRankTrilinearUniquenessStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankFrobenius equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg
open scoped NNReal

universe uF uV

section Conjugation




end Conjugation

namespace Padic
open Langlands.GodementJacquet.Padic hiding MatrixConverges compactMatrixLaurentBorelSpace compactMatrixLaurentLocalField compactMatrixLaurentMeasurableSpace compactMatrixLaurentTopology compactMatrixLaurentValuativeRel determinantWeight_locallyConstant determinantWeight_shift_spectral exists_laurent_integral_of_hasCompactSupport exists_laurent_matrixIntegral_of_hasCompactSupport exists_smoothFunctional_ne_zero instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instTopologicalSpaceCarrier instValuativeRelCarrier jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues nonzeroZetaLocalField nonzeroZetaTopology nonzeroZetaValuativeRel regularMatrixZetaGLBorel regularMatrixZetaGLMeasurable regularMatrixZetaLocalField regularMatrixZetaOperator regularMatrixZetaOperator_dual regularMatrixZetaTopology regularMatrixZetaValuation weightedRegularMatrixTest weightedRegularMatrixTest_apply whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding MatrixConverges determinantNorm_eq_one_of_mem_conjugateUnipotent determinantUnitTestToMatrixTest determinantUnitTestToMatrixTest_apply determinantUnitTestToMatrixTest_eq_zero hasCompactSupport_determinantUnit_coefficient jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues oneBlockDeterminantUnitHomeomorph supercuspidalCutoffFourierEvaluation supercuspidalCutoffMatrixTest supercuspidalCutoffMatrixTest_apply supercuspidalCutoffMatrixTest_apply_of_not_mem supercuspidalCutoffMatrixTest_fourier_eq_zero_of_stabilizer supercuspidalCutoffMatrixTest_fourier_right supercuspidalCutoffMatrixTest_fourier_singular supercuspidalCutoffMatrixTest_mem_fourierRegularMatrixTests supercuspidalCutoffMatrixTest_right supercuspidalCutoffMatrixTest_singular supercuspidalDeterminantUnitCoefficient whittakerRationalValues
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

variable {m : ℕ} (hm : 0 < m)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GeneralLinear (m + 1) F) V)
  (hρ : GeneralLinear.IsSupercuspidal ρ)
  (ℓ : Module.Dual ℂ V) (hℓ : IsSmoothVector ρ.dual ℓ)

/-- Smooth algebraic functionals separate every nonzero vector of the actual
smooth representation of canonical p-adic GL. -/
theorem exists_smoothFunctional_ne_zero (hρsm : IsSmooth ρ)
    (v : V) (hv : v ≠ 0) :
    ∃ ℓ : Module.Dual ℂ V, IsSmoothVector ρ.dual ℓ ∧ ℓ v ≠ 0 := by
  have hcofinal :
      ∀ K : OpenSubgroup (GeneralLinear (m + 1) F),
        ∃ L : OpenSubgroup (GeneralLinear (m + 1) F),
          IsCompact (L : Set (GeneralLinear (m + 1) F)) ∧ L ≤ K := by
    intro K
    obtain ⟨L, hL, hLK⟩ :=
      (⟨⟩ : LocalFieldData F).generalLinearCompactOpen (m + 1)
        (K : Set (GeneralLinear (m + 1) F))
        (K.isOpen.mem_nhds K.one_mem)
    exact ⟨L, hL, hLK⟩
  have hinj := smoothBidual_injective_of_compact_cofinal hcofinal ρ hρsm
  by_contra h
  push Not at h
  have hz : smoothBidual hρsm v = 0 := by
    apply Subtype.ext
    apply LinearMap.ext
    intro φ
    change φ.val v = 0
    exact h φ.val φ.property
  exact hv (hinj (by simpa only [map_zero] using hz))

end Padic

end Langlands.AllField.GodementJacquet
