import Langlands.Representation.RankinSelberg.AdjacentRankModelStarBase
import Langlands.AllField.HarmonicAnalysis.AdjacentRankUnipotentFourierProof
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelStarFourierOrbit
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelStarReduction
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelStarRegularity
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonUnipotentIota
/-! The fixed-action adjacent-rank model-star identity at the base ambient point. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding AdjacentRankBaseModelStarIdentity AdjacentRankModelConvergenceStatement AdjacentRankModelStarStatement EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneGammaTwistStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement adjacentRankFullFourier adjacentRankFullFourier_inverseTranspose adjacentRankFullFourier_tmul adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelStarBase_of_pure_integrals adjacentRankModelStarIntegrabilityLocalInstance1 adjacentRankModelStarIntegrabilityLocalInstance2 adjacentRankModelStarIntegrabilityLocalInstance3 adjacentRankModelStarIntegrabilityLocalInstance4 adjacentRankModelStarIntegrabilityLocalInstance5 adjacentRankModelStarIntegrabilityLocalInstance6 adjacentRankModelStarIntegrabilityLocalInstance7 adjacentRankModelStarIntegrabilityLocalInstance8 adjacentRankModelStarIntegrabilityLocalInstance9 adjacentRankModelStarSourceFunction_regularity adjacentRankModelStarTargetFunction_regularity adjacentRankModelStar_base adjacentRankModelStar_equality_of_base adjacentRankModelStar_pure_right_averages adjacentRankPure_hasCompactSupport adjacentRankTransformedIntegrand adjacentRankTransformedPure_hasCompactSupport adjacentRankTransformed_integrable_of_isSmooth adjacentRank_distribHaarChar adjacentRank_fullFourier_kernel_reflected_orbit adjacentRank_fullFourier_rowTranslate adjacentRank_inverseTranspose_unipotent_epsilon adjacentRank_kernel_reflected_right_orbit adjacentRank_kernel_right_unipotent adjacentRank_partialFourier_rowTranslate adjacentRank_rho0_kernel_right_orbit continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelStarBaseBorel modelStarBaseDisconnected modelStarBaseGLBorel modelStarBaseGLMeasurable modelStarBaseLocalField modelStarBaseMeasurable modelStarBaseT2 modelStarBaseTopology modelStarBaseUnipotentBorel modelStarBaseUnipotentMeasurable modelStarBaseValuative modelStarFourierBorel modelStarFourierDisconnected modelStarFourierLocalField modelStarFourierMeasurable modelStarFourierT2 modelStarFourierTopology modelStarFourierValuative modelStarOrbitFourierBorel modelStarOrbitFourierDisconnected modelStarOrbitFourierLocalField modelStarOrbitFourierMeasurable modelStarOrbitFourierSecondCountable modelStarOrbitFourierT2 modelStarOrbitFourierTopology modelStarOrbitFourierValuative modelStarReductionBorel modelStarReductionDisconnected modelStarReductionGLBorel modelStarReductionGLMeasurable modelStarReductionLocalField modelStarReductionMeasurable modelStarReductionT2 modelStarReductionTopology modelStarReductionValuative modelStarRegularityLocalField modelStarRegularityTopology modelStarRegularityValuative normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory TensorProduct Matrix
open Langlands.HarmonicAnalysis hiding AdjacentRankUnipotentFourierStatement PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement adjacentRankUnipotentFourier padicMatrixFourierSlice padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicScalarHaarScaling padicUnipotentHaar_iota_fourier_duality_right
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear

universe uF uV

section Algebra



end Algebra

section CanonicalTopology

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance modelStarBaseT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance modelStarBaseMeasurable : MeasurableSpace F := borel _
local instance modelStarBaseBorel : BorelSpace F := ⟨rfl⟩
local instance modelStarBaseDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance modelStarBaseGLMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F) := borel _
local instance modelStarBaseGLBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F) := ⟨rfl⟩
local instance modelStarBaseUnipotentMeasurable (r : ℕ) :
    MeasurableSpace (upperUnipotent (r + 1) F) := borel _
local instance modelStarBaseUnipotentBorel (r : ℕ) :
    BorelSpace (upperUnipotent (r + 1) F) := ⟨rfl⟩

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
  (hself : IsSelfDual ψ ν) {r : ℕ}
  (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
  (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F)

/-- The scalar Fourier theorem compares the source orbit at `h` with the
target orbit at `iota(h) * w`, retaining the Weyl character constant. -/
theorem adjacentRankModelStar_pure_right_averages
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (h : GeneralLinear (r + 1) F) :
    (∫ u : upperUnipotent (r + 1) F,
      adjacentRankModelStarSourceFunction ψ σ ℓ
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) χ ((r : ℂ) / 2)
        (adjacentRankRho0 ψ ν hself σ ℓ
          (adjacentRankModelStarBasePoint (F := F) r) (Φ ⊗ₜ W))
        (h * u.val) ∂unipotentHaar F r) =
      (χ (determinant (weylLong (r + 1) F)) : ℂ) *
        ∫ u : upperUnipotent (r + 1) F,
          adjacentRankModelStarTargetFunction ψ σ ℓ
            (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) χ ((r : ℂ) / 2)
            (adjacentRankFullFourier F ψ ν hself σ ℓ (Φ ⊗ₜ W))
            ((inverseTranspose (r + 1) F h * weylLong (r + 1) F) *
              u.val) ∂unipotentHaar F r := by
  let φ := adjacentRankRowTranslate h
    ((partialFourierEquiv ψ ν (r + 1) hself).symm Φ)
  let L : upperUnipotent (r + 1) F → ℂ := fun u =>
    partialFourierEquiv ψ ν (r + 1) hself
      (rectangularTranslate (adjacentRankModelStarBasePoint (F := F) r) φ)
      (rectangularJoin u.val.val (adjacentRankEpsilon F r)) *
        (inverseStandardCharacter ψ r u : ℂ)
  let R : upperUnipotent (r + 1) F → ℂ := fun u =>
    rectangularFourierEquiv ψ ν (r + 1) (r + 2) hself
      (partialFourierEquiv ψ ν (r + 1) hself φ)
      (rectangularJoin ((weylLong (r + 1) F).val * u.val.val)
        ((weylLong (r + 1) F).val *ᵥ adjacentRankEpsilon F r)) *
          (standardCharacter ψ r u : ℂ)
  let A := glModelFunction ψ r σ ℓ W h⁻¹ * (χ (determinant h) : ℂ) *
    determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) h ((r : ℂ) / 2) *
    determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) h 1
  have hL (u : upperUnipotent (r + 1) F) :
      adjacentRankModelStarSourceFunction ψ σ ℓ
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) χ ((r : ℂ) / 2)
        (adjacentRankRho0 ψ ν hself σ ℓ
          (adjacentRankModelStarBasePoint (F := F) r) (Φ ⊗ₜ W)) (h * u.val) =
        A * L u := by
    simp only [adjacentRankModelStarSourceFunction, adjacentRankRho0_tmul,
      adjacentRankTestEvaluation_tmul]
    rw [adjacentRank_rho0_kernel_right_orbit F ψ ν hself,
      adjacentRank_coefficient_right_orbit ψ σ ℓ,
      adjacentRank_determinant_right_unipotent,
      adjacentRank_determinantWeight_right_unipotent]
    dsimp only [A, L, φ]
    simp only [inverseStandardCharacter_apply, standardCharacter_apply]
    ring
  have hc : (χ (determinant (weylLong (r + 1) F)) : ℂ) *
      ((χ⁻¹) (determinant (weylLong (r + 1) F)) : ℂ) = 1 := by
    change ((χ (determinant (weylLong (r + 1) F)) : ℂˣ) : ℂ) *
      (((χ (determinant (weylLong (r + 1) F)))⁻¹ : ℂˣ) : ℂ) = 1
    rw [← Units.val_mul, mul_inv_cancel]
    rfl
  have hR (u : upperUnipotent (r + 1) F) :
      A * R u =
        (χ (determinant (weylLong (r + 1) F)) : ℂ) *
          adjacentRankModelStarTargetFunction ψ σ ℓ
            (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) χ ((r : ℂ) / 2)
            (adjacentRankFullFourier F ψ ν hself σ ℓ (Φ ⊗ₜ W))
            ((inverseTranspose (r + 1) F h * weylLong (r + 1) F) *
              u.val) := by
    simp only [adjacentRankModelStarTargetFunction, adjacentRankFullFourier_tmul,
      adjacentRankTestEvaluation_tmul]
    rw [adjacentRank_coefficient_reflected_right_orbit ψ σ ℓ,
      adjacentRank_determinant_right_unipotent,
      adjacentRank_determinantWeight_right_unipotent,
      adjacentRank_inverse_character_reflected_base,
      adjacentRank_determinantWeight_reflected_base]
    dsimp only [A, R, φ]
    rw [adjacentRank_fullFourier_kernel_reflected_orbit F ψ ν hself]
    calc
      _ = (determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          h ((r : ℂ) / 2) *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) h 1 *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          h (-((r + 1 : ℕ) : ℂ))) *
        (glModelFunction ψ r σ ℓ W h⁻¹ * (χ (determinant h) : ℂ) *
          rectangularFourierEquiv ψ ν (r + 1) (r + 2) hself Φ
            (adjacentRankKernelMatrix
              ((inverseTranspose (r + 1) F h * weylLong (r + 1) F) *
                u.val)) * (standardCharacter ψ r u : ℂ)) := by ring
      _ = _ := by
        rw [adjacentRankModelStar_weight_balance]
        calc
          _ = ((χ (determinant (weylLong (r + 1) F)) : ℂ) *
              ((χ⁻¹) (determinant (weylLong (r + 1) F)) : ℂ)) *
            (rectangularFourierEquiv ψ ν (r + 1) (r + 2) hself Φ
              (adjacentRankKernelMatrix
                ((inverseTranspose (r + 1) F h * weylLong (r + 1) F) *
                  u.val)) *
              ((standardCharacter ψ r u : ℂ) * glModelFunction ψ r σ ℓ W h⁻¹) *
              (χ (determinant h) : ℂ) *
              determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
                h (-((r : ℂ) / 2))) := by rw [hc, one_mul]; ring
          _ = _ := by ring
  have he : (∫ u, L u ∂unipotentHaar F r) =
      ∫ u, R u ∂unipotentHaar F r :=
    (adjacentRankUnipotentFourier F ψ ν hself r φ).2.2
  simp_rw [hL]
  rw [integral_const_mul, he, ← integral_const_mul]
  simp_rw [hR]
  exact integral_const_mul _ _

include hσ in
/-- The pure-tensor integral comparison extends by actual integrability to all
test tensors, after which the base prefactor cancels the Weyl scalar. -/
theorem adjacentRankModelStarBase_of_pure_integrals
    (hpure : ∀
      (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
      (W : (glCoefficientModel ψ r σ ℓ).toSubmodule),
      (∫ h, adjacentRankModelStarSourceFunction ψ σ ℓ
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) χ ((r : ℂ) / 2)
        (adjacentRankRho0 ψ ν hself σ ℓ
          (adjacentRankModelStarBasePoint (F := F) r) (Φ ⊗ₜ W)) h
        ∂generalLinearHaar F r) =
      (χ (determinant (weylLong (r + 1) F)) : ℂ) *
        ∫ h, adjacentRankModelStarTargetFunction ψ σ ℓ
          (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) χ ((r : ℂ) / 2)
          (adjacentRankFullFourier F ψ ν hself σ ℓ (Φ ⊗ₜ W)) h
          ∂generalLinearHaar F r) :
    AdjacentRankBaseModelStarIdentity F ψ ν hself σ ℓ χ := by
  have hall (Ψ : adjacentRankTestSpace ψ σ ℓ) :
      (∫ h, adjacentRankModelStarSourceFunction ψ σ ℓ
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) χ ((r : ℂ) / 2)
        (adjacentRankRho0 ψ ν hself σ ℓ
          (adjacentRankModelStarBasePoint (F := F) r) Ψ) h
        ∂generalLinearHaar F r) =
      (χ (determinant (weylLong (r + 1) F)) : ℂ) *
        ∫ h, adjacentRankModelStarTargetFunction ψ σ ℓ
          (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) χ ((r : ℂ) / 2)
          (adjacentRankFullFourier F ψ ν hself σ ℓ Ψ) h
          ∂generalLinearHaar F r := by
    induction Ψ using adjacentRankTestSpace_induction ψ σ ℓ with
    | tmul Φ W => exact hpure Φ W
    | add Ψ₁ Ψ₂ h₁ h₂ =>
      have hf₁ := adjacentRankModelStarSourceFunction_regularity F ψ r σ hσ ℓ χ
        ((r : ℂ) / 2) (adjacentRankRho0 ψ ν hself σ ℓ
          (adjacentRankModelStarBasePoint (F := F) r) Ψ₁)
      have hf₂ := adjacentRankModelStarSourceFunction_regularity F ψ r σ hσ ℓ χ
        ((r : ℂ) / 2) (adjacentRankRho0 ψ ν hself σ ℓ
          (adjacentRankModelStarBasePoint (F := F) r) Ψ₂)
      have hq₁ := adjacentRankModelStarTargetFunction_regularity F ψ r σ hσ ℓ χ
        ((r : ℂ) / 2) (adjacentRankFullFourier F ψ ν hself σ ℓ Ψ₁)
      have hq₂ := adjacentRankModelStarTargetFunction_regularity F ψ r σ hσ ℓ χ
        ((r : ℂ) / 2) (adjacentRankFullFourier F ψ ν hself σ ℓ Ψ₂)
      simp only [map_add, adjacentRankModelStarSourceFunction_add,
        adjacentRankModelStarTargetFunction_add, Pi.add_apply]
      rw [integral_add (hf₁.1.integrable_of_hasCompactSupport hf₁.2)
        (hf₂.1.integrable_of_hasCompactSupport hf₂.2),
        integral_add (hq₁.1.integrable_of_hasCompactSupport hq₁.2)
          (hq₂.1.integrable_of_hasCompactSupport hq₂.2), h₁, h₂, mul_add]
  intro Ψ
  change (χ (determinant (adjacentRankModelStarBasePoint (F := F) r)) : ℂ) *
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        (adjacentRankModelStarBasePoint (F := F) r) (((r + 1 : ℕ) : ℂ) / 2) *
      (∫ h, adjacentRankModelStarSourceFunction ψ σ ℓ
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) χ ((r : ℂ) / 2)
        (adjacentRankRho0 ψ ν hself σ ℓ
          (adjacentRankModelStarBasePoint (F := F) r) Ψ) h
        ∂generalLinearHaar F r) = _
  rw [hall, ← mul_assoc, adjacentRankModelStarBasePoint_prefactor, one_mul]
  apply integral_congr_ae
  filter_upwards [] with h
  simp only [adjacentRankTransformedIntegrand, adjacentRankRho0_one,
    adjacentRankModelStarTargetFunction]

include hσ in
/-- The fixed-character model-star identity at the ambient point `w * zeta`,
for every smooth representation and every original test tensor. -/
theorem adjacentRankModelStar_base :
    AdjacentRankBaseModelStarIdentity F ψ ν hself σ ℓ χ := by
  apply adjacentRankModelStarBase_of_pure_integrals F ψ ν hself σ hσ ℓ χ
  intro Φ W
  have hf := adjacentRankModelStarSourceFunction_regularity F ψ r σ hσ ℓ χ
    ((r : ℂ) / 2) (adjacentRankRho0 ψ ν hself σ ℓ
      (adjacentRankModelStarBasePoint (F := F) r) (Φ ⊗ₜ W))
  have hq := adjacentRankModelStarTargetFunction_regularity F ψ r σ hσ ℓ χ
    ((r : ℂ) / 2) (adjacentRankFullFourier F ψ ν hself σ ℓ (Φ ⊗ₜ W))
  exact adjacentRank_integral_eq_of_reflected_right_averages F r
    _ _ hf.1 hf.2 hq.1 hq.2 (χ (determinant (weylLong (r + 1) F)))
    (adjacentRankModelStar_pure_right_averages F ψ ν hself σ ℓ χ Φ W)

end CanonicalTopology

end Langlands.AllField.RankinSelberg
