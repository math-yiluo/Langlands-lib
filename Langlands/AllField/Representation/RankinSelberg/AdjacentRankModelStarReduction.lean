import Langlands.Representation.RankinSelberg.AdjacentRankModelStarReduction
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelMap
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelStarFourierCovariance
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelStarIntegrability
/-! Reduction of the model-star equality to its base ambient point. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding AdjacentRankBaseModelStarIdentity AdjacentRankModelConvergenceStatement AdjacentRankModelStarStatement EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneGammaTwistStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement adjacentRankFullFourier adjacentRankFullFourier_inverseTranspose adjacentRankFullFourier_tmul adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelStarIntegrabilityLocalInstance1 adjacentRankModelStarIntegrabilityLocalInstance2 adjacentRankModelStarIntegrabilityLocalInstance3 adjacentRankModelStarIntegrabilityLocalInstance4 adjacentRankModelStarIntegrabilityLocalInstance5 adjacentRankModelStarIntegrabilityLocalInstance6 adjacentRankModelStarIntegrabilityLocalInstance7 adjacentRankModelStarIntegrabilityLocalInstance8 adjacentRankModelStarIntegrabilityLocalInstance9 adjacentRankModelStar_equality_of_base adjacentRankPure_hasCompactSupport adjacentRankTransformedIntegrand adjacentRankTransformedPure_hasCompactSupport adjacentRankTransformed_integrable_of_isSmooth adjacentRank_distribHaarChar continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelStarFourierBorel modelStarFourierDisconnected modelStarFourierLocalField modelStarFourierMeasurable modelStarFourierT2 modelStarFourierTopology modelStarFourierValuative modelStarReductionBorel modelStarReductionDisconnected modelStarReductionGLBorel modelStarReductionGLMeasurable modelStarReductionLocalField modelStarReductionMeasurable modelStarReductionT2 modelStarReductionTopology modelStarReductionValuative normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory TensorProduct
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement padicMatrixFourierSlice padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open scoped NNReal ENNReal Pointwise

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance modelStarReductionT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance modelStarReductionMeasurable : MeasurableSpace F := borel _
local instance modelStarReductionBorel : BorelSpace F := ⟨rfl⟩
local instance modelStarReductionDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance modelStarReductionGLMeasurable (r : ℕ) : MeasurableSpace (GeneralLinear (r + 1) F) := borel _
local instance modelStarReductionGLBorel (r : ℕ) : BorelSpace (GeneralLinear (r + 1) F) := ⟨rfl⟩

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
  (hself : IsSelfDual ψ ν) {r : ℕ}
  (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
  (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F)

/-- The remaining model-star equality at `w * zeta`, for every test tensor.
This is an internal reduction condition, not an assumption of the final target. -/
def AdjacentRankBaseModelStarIdentity : Prop :=
  ∀ Ψ : adjacentRankTestSpace ψ σ ℓ,
    Langlands.AllField.RankinSelberg.Padic.adjacentRankModelIntegral F ψ ν hself σ ℓ χ Ψ
        (weylLong (r + 2) F * adjacentRankZeta F r) =
      ∫ h, adjacentRankTransformedIntegrand F ψ ν hself σ ℓ χ
        (adjacentRankFullFourier F ψ ν hself σ ℓ Ψ) 1 h
        ∂generalLinearHaar F r

private theorem weight_inverseTranspose' {d : ℕ}
    (k : GeneralLinear d F) (s : ℂ) :
    determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        (inverseTranspose d F k) s =
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) k (-s) := by
  unfold determinantWeight
  change (((normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
    (determinant (inverseTranspose d F k) : F) : ℝ) : ℂ) ^ s = _
  rw [RankOneGammaTwist.determinant_inverseTranspose, Units.val_inv_eq_inv_val, map_inv₀,
    Complex.ofReal_inv, Complex.inv_cpow, Complex.cpow_neg]
  · rfl
  · rw [Complex.arg_ofReal_of_nonneg
      ((normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)).nonneg _)]
    exact Real.pi_ne_zero.symm

private theorem weight_exponent_add' {d : ℕ}
    (k : GeneralLinear d F) (s t : ℂ) :
    determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) k (s + t) =
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) k s *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) k t :=
  Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
    ((normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)).ne_zero k.det_ne_zero))

/-- Full Fourier covariance extends the base identity to every ambient point,
with exactly the determinant prefactor of the published model-star statement. -/
theorem adjacentRankModelStar_equality_of_base
    (hbase : AdjacentRankBaseModelStarIdentity F ψ ν hself σ ℓ χ)
    (Ψ : adjacentRankTestSpace ψ σ ℓ) (g : GeneralLinear (r + 2) F) :
    Langlands.AllField.RankinSelberg.Padic.adjacentRankModelIntegral F ψ ν hself σ ℓ χ Ψ
        (weylLong (r + 2) F * inverseTranspose (r + 2) F g) =
      (χ⁻¹ (determinant (adjacentRankZeta F r * g)) : ℂ) *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          (adjacentRankZeta F r * g) (((r + 1 : ℕ) : ℂ) / 2) *
        ∫ h, adjacentRankTransformedIntegrand F ψ ν hself σ ℓ χ
          (adjacentRankFullFourier F ψ ν hself σ ℓ Ψ)
          (adjacentRankZeta F r * g) h ∂generalLinearHaar F r := by
  let k := adjacentRankZeta F r * g
  let a₀ := weylLong (r + 2) F * adjacentRankZeta F r
  have ha : a₀ * inverseTranspose (r + 2) F k =
      weylLong (r + 2) F * inverseTranspose (r + 2) F g := by
    simp only [a₀, k, map_mul, adjacentRankZeta_inverseTranspose, mul_assoc]
    rw [← mul_assoc (adjacentRankZeta F r),
      adjacentRankZeta_mul_self, one_mul]
  rw [← ha, Langlands.AllField.RankinSelberg.Padic.adjacentRankModelIntegral_mul]
  rw [hbase]
  rw [adjacentRankFullFourier_inverseTranspose]
  have hI : (fun h => adjacentRankTransformedIntegrand F ψ ν hself σ ℓ χ
        (determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) k
          ((r + 1 : ℕ) : ℂ) •
          adjacentRankRho0 ψ ν hself σ ℓ k (adjacentRankFullFourier F ψ ν hself σ ℓ Ψ)) 1 h) =
      fun h => determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) k
          ((r + 1 : ℕ) : ℂ) *
        adjacentRankTransformedIntegrand F ψ ν hself σ ℓ χ
          (adjacentRankFullFourier F ψ ν hself σ ℓ Ψ) k h := by
    funext h
    simp only [adjacentRankTransformedIntegrand, adjacentRankRho0_one,
      adjacentRankTestEvaluation_smul]
    ring
  rw [hI, integral_const_mul]
  have hχ : (χ (determinant (inverseTranspose (r + 2) F k)) : ℂ) =
      (χ⁻¹ (determinant k) : ℂ) := by
    simp only [RankOneGammaTwist.determinant_inverseTranspose, map_inv]
    rfl
  have hw : determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        (inverseTranspose (r + 2) F k) (((r + 1 : ℕ) : ℂ) / 2) *
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) k
        ((r + 1 : ℕ) : ℂ) =
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) k
        (((r + 1 : ℕ) : ℂ) / 2) := by
    rw [weight_inverseTranspose', ← weight_exponent_add']
    congr 1
    ring
  rw [hχ, mul_assoc, ← mul_assoc (determinantWeight _ _ _), hw]
  simp only [mul_assoc]
  rfl

end Langlands.AllField.RankinSelberg
