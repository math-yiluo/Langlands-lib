import Langlands.Representation.RankinSelberg.AdjacentRankModelStarFourierCovariance
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelStarStatement
import Langlands.AllField.Representation.RankinSelberg.RankOneGammaTwistStatement
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierTransport
/-! Fixed-character full Fourier covariance for the adjacent-rank model-star
identity, expressed with the normalized determinant weight. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding AdjacentRankModelStarStatement EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement RankOneGammaTwistStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement adjacentRankFullFourier adjacentRankFullFourier_inverseTranspose adjacentRankFullFourier_tmul adjacentRank_distribHaarChar isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt modelStarFourierBorel modelStarFourierDisconnected modelStarFourierLocalField modelStarFourierMeasurable modelStarFourierT2 modelStarFourierTopology modelStarFourierValuative normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory TensorProduct
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement padicMatrixFourierSlice padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open scoped NNReal ENNReal Pointwise

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance modelStarFourierT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance modelStarFourierMeasurable : MeasurableSpace F := borel _
local instance modelStarFourierBorel : BorelSpace F := ⟨rfl⟩
local instance modelStarFourierDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

/-- The intrinsic Haar character is the supplied residue-normalized absolute
value on units. This is a consequence of the published scalar scaling law. -/
theorem adjacentRank_distribHaarChar
    (ν : AdditiveHaarMeasure F) (a : Fˣ) :
    (distribHaarChar F a : ℝ) =
      normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) (a : F) := by
  let T := (⟨⟩ : LocalFieldData F)
  let S : Set F := T.Integers
  have hS : MeasurableSet S := T.isOpen_integers.measurableSet
  have h0 : ν.measure S ≠ 0 :=
    ne_of_gt (T.isOpen_integers.measure_pos ν.measure ⟨0, T.Integers.zero_mem⟩)
  have htop : ν.measure S ≠ ∞ := T.isCompact_integers.measure_ne_top
  have hs := congrArg (fun μ : Measure F => μ S)
    (padicScalarHaarScaling F T ν.measure a⁻¹)
  change (ν.measure.map (fun x => a⁻¹ • x)) S = _ at hs
  rw [Measure.map_apply (measurable_const_smul _) hS,
    Set.preimage_smul, inv_inv, Measure.smul_apply] at hs
  simp only [map_inv, Units.val_inv_eq_inv_val, inv_inv] at hs
  have he := distribHaarChar_eq_of_measure_smul_eq_mul h0 htop hs
  exact congrArg (fun x : ℝ≥0 => (x : ℝ)) he

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
  (hself : IsSelfDual ψ ν) {r : ℕ}
  (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
  (ℓ : glFunctionals ψ r σ)

/-- Full plus Fourier transform of the Schwartz factor, keeping the actual
original coefficient factor and its character unchanged. -/
def adjacentRankFullFourier :
    adjacentRankTestSpace ψ σ ℓ →ₗ[ℂ] adjacentRankTestSpace ψ σ ℓ :=
  TensorProduct.map
    (rectangularFourierEquiv ψ ν (r + 1) (r + 2) hself).toLinearMap LinearMap.id

@[simp] theorem adjacentRankFullFourier_tmul
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule) :
    adjacentRankFullFourier F ψ ν hself σ ℓ (Φ ⊗ₜ W) =
      rectangularFourierEquiv ψ ν (r + 1) (r + 2) hself Φ ⊗ₜ W := rfl

/-- Fourier covariance at the inverse transpose, with its scalar expressed
using the same normalized absolute value as the model integral. -/
theorem adjacentRankFullFourier_inverseTranspose
    (k : GeneralLinear (r + 2) F) (Ψ : adjacentRankTestSpace ψ σ ℓ) :
    adjacentRankFullFourier F ψ ν hself σ ℓ
        (adjacentRankRho0 ψ ν hself σ ℓ (inverseTranspose (r + 2) F k) Ψ) =
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) k
          (((r + 1 : ℕ) : ℂ)) •
        adjacentRankRho0 ψ ν hself σ ℓ k
          (adjacentRankFullFourier F ψ ν hself σ ℓ Ψ) := by
  have hc :
      ((((distribHaarChar F
          (determinant (inverseTranspose (r + 2) F k)) : ℝ) : ℂ) ^
            (r + 1))⁻¹) =
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) k
          (((r + 1 : ℕ) : ℂ)) := by
    rw [RankOneGammaTwist.determinant_inverseTranspose, map_inv, NNReal.coe_inv, Complex.ofReal_inv,
      inv_pow, inv_inv, adjacentRank_distribHaarChar F ν]
    simp only [determinantWeight, Complex.cpow_natCast]
    rfl
  induction Ψ using adjacentRankTestSpace_induction ψ σ ℓ with
  | tmul Φ W =>
    simp only [adjacentRankRho0_tmul, adjacentRankFullFourier_tmul]
    rw [rectangularRho0FourierCovariance ψ ν (r + 1) hself
      (inverseTranspose (r + 2) F k) Φ]
    simp only [inverseTranspose_involutive, hc, smul_tmul']
  | add Ψ₁ Ψ₂ h₁ h₂ =>
    simp only [map_add, h₁, h₂, smul_add]

end Langlands.AllField.RankinSelberg
