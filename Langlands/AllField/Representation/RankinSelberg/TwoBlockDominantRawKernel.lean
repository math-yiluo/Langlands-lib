import Langlands.Representation.RankinSelberg.TwoBlockDominantRawKernel
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientData
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerUnfoldingIntegrandData
/-!
# Raw scalar data for JPSS Section 4.10

The coefficient and determinant weight are evaluated on actual representatives.
The final rectangle covariance is specialized to the constructed matrix and residual
unipotent from `TwoBlockDominantCovarianceData`.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding determinantWeight_lowerBlockUnipotent_mul kernel kernel_covariance kernel_eq rawKernel rawKernel_covariance rawScalarValue
open Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerUnfolding hiding groupIntegrand groupIntegrand_def groupIntegrand_lowerBlockUnipotent_mul integrand integrand_mk integrand_mk_eq_groupIntegrand isTopologicalRing_carrier partialSection partialSection_apply partialSection_lowerBlockUnipotent_mul rowMeasure_map_vecMul_upperUnipotent scalarSection_lowerBlockUnipotent_mul sigmaFinite_additiveHaarMeasure whittaker_blockRotation_lowerBlockUnipotent_mul
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding

universe uF uW

variable {F : Type uF} [Field F]
variable {t r j k : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {ψ : UnitaryAdditiveCharacter F}
variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
variable (f : Sections F h σ)
variable (Wtest : WhittakerFunctions ψ r)

/-- The actual scalar section and test coefficient, before choosing the large-group
matrix argument. -/
def rawScalarValue (g : GeneralLinear (t + 1) F)
    (P : GeneralLinear (r + 1) F) : ℂ :=
  scalarSection (fun i => (ell i).val) f g 1 * Wtest.val P

/-- The determinant weight on a lower-unipotent translate is unchanged for any complex
exponent. This uses the determinant-one law of the actual lower subgroup. -/
theorem determinantWeight_lowerBlockUnipotent_mul (z : ℂ)
    (u : lowerBlockUnipotent h F) (g : GeneralLinear (t + 1) F) :
    determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (u.val * g) z =
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g z := by
  have hd : Matrix.det u.val.val = 1 := by
    simpa only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] using
      congrArg (fun a : Fˣ => (a : F))
        (determinant_eq_one_of_mem_lowerBlockUnipotent h F u.property)
  simp only [determinantWeight, Units.val_mul, Matrix.det_mul, hd, one_mul]

/-- Algebraic cancellation at actual matrix arguments. The later rectangle theorem supplies
`v` and its character law from the residual-unipotent construction. -/
private theorem rawScalarValue_cancel
    (u : lowerBlockUnipotent h F) (v : upperUnipotent (r + 1) F)
    (hv : standardCharacter ψ r v =
        ∏ i, standardCharacter ψ (m i) (diagonalBlocks h F u i))
    (g : GeneralLinear (t + 1) F) (P : GeneralLinear (r + 1) F) :
    rawScalarValue ell f Wtest (u.val * g) (v.val * P) =
      rawScalarValue ell f Wtest g P := by
  have h0 : (standardCharacter ψ (m 0) (diagonalBlocks h F u 0) : ℂ) *
      (inverseStandardCharacter ψ (m 0) (diagonalBlocks h F u 0) : ℂ) = 1 :=
    Units.mul_inv _
  have h1 : (standardCharacter ψ (m 1) (diagonalBlocks h F u 1) : ℂ) *
      (inverseStandardCharacter ψ (m 1) (diagonalBlocks h F u 1) : ℂ) = 1 :=
    Units.mul_inv _
  rw [rawScalarValue, rawScalarValue, scalarSection_lowerBlockUnipotent_mul ell f u g,
    Wtest.property v P, hv, Fin.prod_univ_two, Fin.prod_univ_two, Units.val_mul]
  calc _ =
      ((standardCharacter ψ (m 0) (diagonalBlocks h F u 0) : ℂ) *
        (inverseStandardCharacter ψ (m 0) (diagonalBlocks h F u 0) : ℂ)) *
      ((standardCharacter ψ (m 1) (diagonalBlocks h F u 1) : ℂ) *
        (inverseStandardCharacter ψ (m 1) (diagonalBlocks h F u 1) : ℂ)) *
      (scalarSection (fun i => (ell i).val) f g 1 * Wtest.val P) := by ring
    _ = _ := by rw [h0, h1, one_mul, one_mul]

/-- Cancellation for the computed residual, with its character supplied by the
constructed matrices rather than by a hypothesis on the caller. -/
private theorem rawScalarValue_residual
    (hr : r=t+(j+k+1)) (u : lowerBlockUnipotent h F)
    (x : Matrix (Fin (m 0+1)) (Fin k) F)
    (y : Matrix (Fin j) (Fin (m 1+1)) F)
    (g : GeneralLinear (t+1) F) (P : GeneralLinear (r+1) F) :
    rawScalarValue ell f Wtest (u.val * g) ((residualUnipotent h hr u x y).val * P) =
      rawScalarValue ell f Wtest g P := by
  apply rawScalarValue_cancel
  simpa only [Fin.prod_univ_two] using residualUnipotent_character h hr u x y ψ

/-- The unweighted scalar kernel at the actual Section 4.10 matrix. -/
def rawKernel (hr : r=t+(j+k+1)) (g : GeneralLinear (t+1) F)
    (x : Matrix (Fin (m 0+1)) (Fin k) F)
    (y : Matrix (Fin j) (Fin (m 1+1)) F) : ℂ :=
  rawScalarValue ell f Wtest g (matrix h hr g x y)

/-- The representative-level kernel of Section 4.10(2), with its actual determinant
weight and with all inverse block Whittaker functionals, including zero. -/
def kernel (hr : r=t+(j+k+1)) (s : ℂ) (g : GeneralLinear (t+1) F)
    (x : Matrix (Fin (m 0+1)) (Fin k) F)
    (y : Matrix (Fin j) (Fin (m 1+1)) F) : ℂ :=
  rawKernel ell f Wtest hr g x y *
    determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
      (s - ((j+k+1 : ℕ) : ℂ)/2 + (j : ℂ))

/-- Evaluation of the kernel on the actual section, coefficient and matrix. -/
theorem kernel_eq (hr : r=t+(j+k+1)) (s : ℂ) (g : GeneralLinear (t+1) F)
    (x : Matrix (Fin (m 0+1)) (Fin k) F)
    (y : Matrix (Fin j) (Fin (m 1+1)) F) :
    kernel ell f Wtest hr s g x y =
      scalarSection (fun i => (ell i).val) f g 1 * Wtest.val (matrix h hr g x y) *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
          (s - ((j+k+1 : ℕ) : ℂ)/2 + (j : ℂ)) := rfl

/-- The actual unweighted kernel is covariant under the simultaneous rectangle
change computed from the lower-group element. -/
theorem rawKernel_covariance (hr : r=t+(j+k+1))
    (u : lowerBlockUnipotent h F) (g : GeneralLinear (t+1) F)
    (x : Matrix (Fin (m 0+1)) (Fin k) F)
    (y : Matrix (Fin j) (Fin (m 1+1)) F) :
    rawKernel ell f Wtest hr (u.val * g) x y =
      rawKernel ell f Wtest hr g
        ((rectangleChange h j k u (x,y)).1) ((rectangleChange h j k u (x,y)).2) := by
  unfold rawKernel
  rw [matrix_covariance h hr u g x y]
  exact rawScalarValue_residual ell f Wtest hr u x y g _

/-- The weighted representative kernel has the same actual rectangle covariance
for every complex parameter, using determinant one of the lower-group element. -/
theorem kernel_covariance (hr : r=t+(j+k+1)) (s : ℂ)
    (u : lowerBlockUnipotent h F) (g : GeneralLinear (t+1) F)
    (x : Matrix (Fin (m 0+1)) (Fin k) F)
    (y : Matrix (Fin j) (Fin (m 1+1)) F) :
    kernel ell f Wtest hr s (u.val * g) x y =
      kernel ell f Wtest hr s g
        ((rectangleChange h j k u (x,y)).1) ((rectangleChange h j k u (x,y)).2) := by
  unfold kernel
  rw [rawKernel_covariance ell f Wtest hr u g x y,
    determinantWeight_lowerBlockUnipotent_mul]

end Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
