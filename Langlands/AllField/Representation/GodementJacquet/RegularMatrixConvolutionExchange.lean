import Langlands.Representation.GodementJacquet.RegularMatrixConvolutionExchange
import Langlands.AllField.HarmonicAnalysis.SquareFourierCrossExchange
import Langlands.AllField.Representation.GodementJacquet.InverseTransposeMatrixIntegral
import Langlands.AllField.Representation.GodementJacquet.RegularMatrixHaarDensity
/-! Actual convolution exchange for Fourier-regular matrix tests. -/

noncomputable section

namespace Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData aestronglyMeasurable_dualParabolicIntegrand compactMatrixLaurentBorelSpace compactMatrixLaurentLocalField compactMatrixLaurentMeasurableSpace compactMatrixLaurentTopology compactMatrixLaurentValuativeRel convolutionExchangeBorel convolutionExchangeDisconnected convolutionExchangeGLBorel convolutionExchangeGLMeasurable convolutionExchangeLocalField convolutionExchangeMeasurable convolutionExchangeT2 convolutionExchangeTopology convolutionExchangeValuation determinantWeight_inv_inverseTranspose determinantWeight_locallyConstant determinantWeight_neg_dimension determinantWeight_shift_spectral dualParabolicBorelSpace dualParabolicGLBorelSpace dualParabolicGLMeasurableSpace dualParabolicIntegrand dualParabolicLocalField dualParabolicMatrixSecondCountable dualParabolicMeasurableSpace dualParabolicSecondCountable dualParabolicT2Space dualParabolicTopology dualParabolicTotallyDisconnected dualParabolicValuativeRel dualWeightedRegularMatrixTest dualWeightedRegularMatrixTest_apply dualWeightedRegularMatrixTest_convolution_cross dualWeightedRegularMatrixTest_convolution_left dualWeightedRegularMatrixTest_convolution_right exists_integral_regularMatrix_density exists_laurent_integral_of_hasCompactSupport exists_laurent_matrixIntegral_of_hasCompactSupport generalLinearHaar_measurePreserving_inverseTranspose instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 integrable_comp_lowerLeft integrable_integral_dualParabolicIntegrand integrable_integral_dualParabolic_levi integral_comp_lowerLeft iotaMatrixRationalValues jpssI2 jpssI3 map_mulLeftMeasurableEquiv matrixIntegral matrixIntegrand matrixRationalValues measurable_inverseTranspose_val mulLeftMeasurableEquiv mulLeftMeasurableEquiv_apply rectangularFourierEquiv_inverseTranspose_translate rectangularFourierEquiv_inverseTranspose_translate_of_mem regularDensityBorel regularDensityGLBorel regularDensityGLMeasurable regularDensityLocalField regularDensityMeasurable regularDensitySecondCountable regularDensityT2 regularDensityTopology regularDensityValuation regularMatrixZetaGLBorel regularMatrixZetaGLMeasurable regularMatrixZetaLocalField regularMatrixZetaOperator regularMatrixZetaOperator_dual regularMatrixZetaOperator_inverseTranspose regularMatrixZetaOperator_inverseTranspose_cross regularMatrixZetaTopology regularMatrixZetaValuation weightedRegularMatrixTest weightedRegularMatrixTest_apply whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues whittakerRationalValues
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement PadicSelfDualMeasureExistsStatement measurePreserving_rectangular_mul_mul padicLatticeGeometry padicRectangularFourierIntegral_exchange_left padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicScalarHaarScaling padicSelfDualMeasureExists padicSquareFourierIntegral_crossExchange padicSquareFourierIntegral_transposeRight rectangularFourierIntegral_comp_mul_mul rectangularFourierIntegral_translate_decomposition rectangularPairing_mul_mul
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFunctionalEquationStatement IsPadicPairGammaFactor LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map disjoint_determinantSlice equalRankContinuedForms equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def exists_rankOneCutoff exists_rankOneEmbedding_support iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice rankOneModelValues_subset_whittakerRationalValues rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg
open scoped NNReal

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance convolutionExchangeT2 : T2Space F :=
  (⟨⟩ : LocalFieldData F).fieldT2
local instance convolutionExchangeDisconnected : TotallyDisconnectedSpace F :=
  (padicLatticeGeometry F (⟨⟩ : LocalFieldData F)).1
local instance convolutionExchangeMeasurable : MeasurableSpace F := borel _
local instance convolutionExchangeBorel : BorelSpace F := ⟨rfl⟩
local instance convolutionExchangeGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance convolutionExchangeGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩

variable {n : ℕ}

/-- The complementary weighted test pulled back by the actual inverse transpose. -/
def dualWeightedRegularMatrixTest (s : ℂ) :
    regularMatrixTests (K := F) (n + 1) →ₗ[ℂ]
      SchwartzBruhat (GeneralLinear (n + 1) F) :=
  (Hecke.TestFunction.pullback
    (GeneralLinear.inverseTransposeContinuous (n + 1) F).toHomeomorph).toLinearMap.comp
      (weightedRegularMatrixTest F ((n + 1 : ℕ) - s))

@[simp] theorem dualWeightedRegularMatrixTest_apply (s : ℂ)
    (Φ : regularMatrixTests (K := F) (n + 1))
    (g : GeneralLinear (n + 1) F) :
    dualWeightedRegularMatrixTest F s Φ g =
      Φ.val (GeneralLinear.inverseTranspose (n + 1) F g).val *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          g (s - (n + 1 : ℕ)) := by
  change Φ.val (GeneralLinear.inverseTranspose (n + 1) F g).val *
    determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
      (GeneralLinear.inverseTranspose (n + 1) F g) ((n + 1 : ℕ) - s) = _
  rw [determinantWeight_inverseTranspose]
  congr 2
  ring

/-- Inverting an inverse transpose leaves the determinant unchanged. -/
theorem determinantWeight_inv_inverseTranspose
    (g : GeneralLinear (n + 1) F) (s : ℂ) :
    determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
      (GeneralLinear.inverseTranspose (n + 1) F g)⁻¹ s =
    determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g s := by
  unfold determinantWeight
  change ((normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g.val.transpose.det : ℂ) ^ s = _
  rw [Matrix.det_transpose]

/-- The left convolution kernel after the measure-preserving inverse transpose. -/
theorem dualWeightedRegularMatrixTest_convolution_left
    (s : ℂ) (Φ Ψ : regularMatrixTests (K := F) (n + 1))
    (k : GeneralLinear (n + 1) F) :
    Hecke.TestFunction.convolution (generalLinearHaar F n)
      (dualWeightedRegularMatrixTest F s Φ) (weightedRegularMatrixTest F s Ψ) k =
    determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) k s *
      ∫ g : GeneralLinear (n + 1) F,
        Φ.val g.val * Ψ.val (g.val.transpose * k.val) *
          determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
            g ((n + 1 : ℕ) : ℂ) ∂generalLinearHaar F n := by
  rw [Hecke.TestFunction.convolution_apply]
  have hμ := generalLinearHaar_measurePreserving_inverseTranspose F n
  rw [← hμ.integral_comp
    (inverseTransposeMeasurableEquiv hμ.measurable).measurableEmbedding]
  calc
    _ = ∫ g : GeneralLinear (n + 1) F,
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) k s *
          (Φ.val g.val * Ψ.val (g.val.transpose * k.val) *
            determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
              g ((n + 1 : ℕ) : ℂ)) ∂generalLinearHaar F n := by
      apply integral_congr_ae
      filter_upwards [] with g
      simp only [dualWeightedRegularMatrixTest_apply, weightedRegularMatrixTest_apply,
        GeneralLinear.inverseTranspose_involutive, determinantWeight_inverseTranspose,
        determinantWeight_mul, determinantWeight_inv_inverseTranspose, Units.val_mul]
      change (Φ.val g.val *
          determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
            g (-(s - (n + 1 : ℕ)))) *
        (Ψ.val (g.val.transpose * k.val) *
          (determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g s *
            determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) k s)) = _
      have hw := determinantWeight_exponent_add
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
        (-(s - (n + 1 : ℕ))) s
      rw [show -(s - (n + 1 : ℕ)) + s = ((n + 1 : ℕ) : ℂ) by ring] at hw
      rw [hw]
      ring
    _ = _ := integral_const_mul _ _

/-- The right convolution kernel expressed with the same determinant density. -/
theorem dualWeightedRegularMatrixTest_convolution_right
    (s : ℂ) (Φ Ψ : regularMatrixTests (K := F) (n + 1))
    (k : GeneralLinear (n + 1) F) :
    Hecke.TestFunction.convolution (generalLinearHaar F n)
      (weightedRegularMatrixTest F s Φ) (dualWeightedRegularMatrixTest F s Ψ) k =
    determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        k (s - (n + 1 : ℕ)) *
      ∫ g : GeneralLinear (n + 1) F,
        Φ.val g.val *
          Ψ.val (g.val.transpose *
            (GeneralLinear.inverseTranspose (n + 1) F k).val) *
          determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
            g ((n + 1 : ℕ) : ℂ) ∂generalLinearHaar F n := by
  rw [Hecke.TestFunction.convolution_apply]
  calc
    _ = ∫ g : GeneralLinear (n + 1) F,
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
            k (s - (n + 1 : ℕ)) *
          (Φ.val g.val *
            Ψ.val (g.val.transpose *
              (GeneralLinear.inverseTranspose (n + 1) F k).val) *
            determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
              g ((n + 1 : ℕ) : ℂ)) ∂generalLinearHaar F n := by
      apply integral_congr_ae
      filter_upwards [] with g
      simp only [weightedRegularMatrixTest_apply, dualWeightedRegularMatrixTest_apply,
        map_mul, map_inv, Units.val_mul, determinantWeight_mul]
      have hi (t : ℂ) :
          determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g⁻¹ t =
            determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g (-t) := by
        simpa only [determinantWeight, GeneralLinear.inverseTranspose_coe,
          Matrix.det_transpose] using
            determinantWeight_inverseTranspose
              (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g t
      rw [hi]
      change (Φ.val g.val *
          determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g s) *
        (Ψ.val (g.val.transpose *
          (GeneralLinear.inverseTranspose (n + 1) F k).val) *
          (determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
              g (-(s - (n + 1 : ℕ))) *
            determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
              k (s - (n + 1 : ℕ)))) = _
      have hw := determinantWeight_exponent_add
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g s (-(s - (n + 1 : ℕ)))
      rw [show s + -(s - (n + 1 : ℕ)) = ((n + 1 : ℕ) : ℂ) by ring] at hw
      rw [hw]
      ring
    _ = _ := integral_const_mul _ _

/-- The Jacobian in square Fourier exchange is the negative dimension weight. -/
theorem determinantWeight_neg_dimension
    (g : GeneralLinear (n + 1) F) :
    determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        g (-((n + 1 : ℕ) : ℂ)) =
      (((((⟨⟩ : LocalFieldData F).determinantNorm (n + 1) g : ℝ≥0) ^
        (n + 1))⁻¹ : ℝ≥0) : ℂ) := by
  simp only [determinantWeight, Complex.cpow_neg, Complex.cpow_natCast,
    NNReal.coe_inv, NNReal.coe_pow, Complex.ofReal_inv, Complex.ofReal_pow]
  rfl

/-- Actual Hecke convolution exchange on tests regular on both Fourier sides. -/
theorem dualWeightedRegularMatrixTest_convolution_cross
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (s : ℂ)
    (Φ Ψ : fourierRegularMatrixTests (K := F) (n + 1) ψ ν hsd) :
    Hecke.TestFunction.convolution (generalLinearHaar F n)
      (dualWeightedRegularMatrixTest F s
        ⟨rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Φ.val, Φ.property.2⟩)
      (weightedRegularMatrixTest F s ⟨Ψ.val, Ψ.property.1⟩) =
    Hecke.TestFunction.convolution (generalLinearHaar F n)
      (weightedRegularMatrixTest F s ⟨Φ.val, Φ.property.1⟩)
      (dualWeightedRegularMatrixTest F s
        ⟨rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Ψ.val, Ψ.property.2⟩) := by
  obtain ⟨c, hc, hden⟩ := exists_integral_regularMatrix_density F n ν
  apply Hecke.TestFunction.ext
  intro k
  let fL (X : Matrix (Fin (n + 1)) (Fin (n + 1)) F) : ℂ :=
    rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Φ.val X *
      Ψ.val (X.transpose * k.val)
  let fR (X : Matrix (Fin (n + 1)) (Fin (n + 1)) F) : ℂ :=
    Φ.val X * rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Ψ.val
      (X.transpose * (GeneralLinear.inverseTranspose (n + 1) F k).val)
  have hL := hden fL (by
    intro X hX
    have hz : rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Φ.val X = 0 :=
      Φ.property.2 X hX
    simp only [fL, hz, zero_mul])
  have hR := hden fR (by
    intro X hX
    simp only [fR, Φ.property.1 X hX, zero_mul])
  have hcross :
      (∫ X, fL X ∂rectangularMeasure ν (n + 1) (n + 1)) =
        (((((⟨⟩ : LocalFieldData F).determinantNorm (n + 1) k : ℝ≥0) ^
          (n + 1))⁻¹ : ℝ≥0) : ℂ) *
          ∫ X, fR X ∂rectangularMeasure ν (n + 1) (n + 1) := by
    simpa only [fL, fR, rectangularFourierEquiv_apply] using
      padicSquareFourierIntegral_crossExchange F (⟨⟩ : LocalFieldData F) (n + 1)
        ψ ν k Φ.val Ψ.val
  have hc0 : (c : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (ne_of_gt hc))
  apply mul_left_cancel₀ hc0
  rw [dualWeightedRegularMatrixTest_convolution_left,
    dualWeightedRegularMatrixTest_convolution_right]
  change (c : ℂ) *
      (determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) k s *
        ∫ g : GeneralLinear (n + 1) F,
          fL g.val * determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
            g ((n + 1 : ℕ) : ℂ) ∂generalLinearHaar F n) =
    (c : ℂ) *
      (determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          k (s - (n + 1 : ℕ)) *
        ∫ g : GeneralLinear (n + 1) F,
          fR g.val * determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
            g ((n + 1 : ℕ) : ℂ) ∂generalLinearHaar F n)
  calc
    _ = determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) k s *
        ((c : ℂ) * ∫ g : GeneralLinear (n + 1) F,
          fL g.val * determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
            g ((n + 1 : ℕ) : ℂ) ∂generalLinearHaar F n) := by ring
    _ = determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) k s *
        ∫ X, fL X ∂rectangularMeasure ν (n + 1) (n + 1) := by rw [hL]
    _ = determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          k (s - (n + 1 : ℕ)) *
        ∫ X, fR X ∂rectangularMeasure ν (n + 1) (n + 1) := by
      rw [hcross, ← determinantWeight_neg_dimension F k, ← mul_assoc,
        ← determinantWeight_exponent_add]
      congr 2
    _ = determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          k (s - (n + 1 : ℕ)) *
        ((c : ℂ) * ∫ g : GeneralLinear (n + 1) F,
          fR g.val * determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
            g ((n + 1 : ℕ) : ℂ) ∂generalLinearHaar F n) := by rw [hR]
    _ = _ := by ring

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Inverse-transpose pullback of the weighted test gives the actual zeta
operator for the representation composed with inverse transpose. -/
theorem regularMatrixZetaOperator_inverseTranspose
    (ρ : Representation ℂ (GeneralLinear (n + 1) F) V)
    (hρ : IsSmooth ρ)
    (hι : IsSmooth (ρ.comp
      (GeneralLinear.inverseTranspose (n + 1) F).toMonoidHom))
    (s : ℂ) (Φ : regularMatrixTests (K := F) (n + 1)) :
    regularMatrixZetaOperator F
      (ρ.comp (GeneralLinear.inverseTranspose (n + 1) F).toMonoidHom)
        hι ((n + 1 : ℕ) - s) Φ =
      Hecke.integratedAction (generalLinearHaar F n) ρ hρ
        (dualWeightedRegularMatrixTest F s Φ) := by
  ext v
  exact Character.integratedAction_comp_automorphism
    (generalLinearHaar F n) ρ hρ
    (GeneralLinear.inverseTransposeContinuous (n + 1) F)
    (generalLinearHaar_measurePreserving_inverseTranspose F n) hι
    (weightedRegularMatrixTest F ((n + 1 : ℕ) - s) Φ) v

/-- The actual original and transformed zeta operators satisfy the cross
identity, with composition in the order supplied by Hecke convolution. -/
theorem regularMatrixZetaOperator_inverseTranspose_cross
    (ρ : Representation ℂ (GeneralLinear (n + 1) F) V)
    (hρ : IsSmooth ρ)
    (hι : IsSmooth (ρ.comp
      (GeneralLinear.inverseTranspose (n + 1) F).toMonoidHom))
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (s : ℂ)
    (Φ Ψ : fourierRegularMatrixTests (K := F) (n + 1) ψ ν hsd) :
    regularMatrixZetaOperator F
        (ρ.comp (GeneralLinear.inverseTranspose (n + 1) F).toMonoidHom)
        hι ((n + 1 : ℕ) - s)
        ⟨rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Φ.val, Φ.property.2⟩ *
      regularMatrixZetaOperator F ρ hρ s ⟨Ψ.val, Ψ.property.1⟩ =
    regularMatrixZetaOperator F ρ hρ s ⟨Φ.val, Φ.property.1⟩ *
      regularMatrixZetaOperator F
        (ρ.comp (GeneralLinear.inverseTranspose (n + 1) F).toMonoidHom)
        hι ((n + 1 : ℕ) - s)
        ⟨rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Ψ.val, Ψ.property.2⟩ := by
  simp_rw [regularMatrixZetaOperator_inverseTranspose F ρ hρ hι]
  ext v
  change Hecke.integratedAction (generalLinearHaar F n) ρ hρ
      (dualWeightedRegularMatrixTest F s
        ⟨rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Φ.val, Φ.property.2⟩)
      (Hecke.integratedAction (generalLinearHaar F n) ρ hρ
        (weightedRegularMatrixTest F s ⟨Ψ.val, Ψ.property.1⟩) v) =
    Hecke.integratedAction (generalLinearHaar F n) ρ hρ
      (weightedRegularMatrixTest F s ⟨Φ.val, Φ.property.1⟩)
      (Hecke.integratedAction (generalLinearHaar F n) ρ hρ
        (dualWeightedRegularMatrixTest F s
          ⟨rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Ψ.val, Ψ.property.2⟩) v)
  rw [← Hecke.integratedAction_convolution, ← Hecke.integratedAction_convolution,
    dualWeightedRegularMatrixTest_convolution_cross F ψ ν hsd s Φ Ψ]

end Langlands.AllField.GodementJacquet.Padic
