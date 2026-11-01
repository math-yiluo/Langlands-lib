import Langlands.Representation.RankinSelberg.AdjacentRankModelMap
import Langlands.Representation.RankinSelberg.AdjacentRankModelStarFourierCovariance
import Langlands.Representation.RankinSelberg.AdjacentRankModelStarIntegrability

/-! Reduction of the model-star equality to its base ambient point. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker TensorProduct GeneralLinear
open scoped NNReal ENNReal Pointwise

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance modelStarReductionTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance modelStarReductionValuative : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance modelStarReductionLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance modelStarReductionT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance modelStarReductionMeasurable : MeasurableSpace F.Carrier := borel _
local instance modelStarReductionBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance modelStarReductionDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance modelStarReductionGLMeasurable (r : ℕ) : MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance modelStarReductionGLBorel (r : ℕ) : BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
  (hself : IsSelfDual ψ ν) {r : ℕ}
  (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F.Carrier)

/-- The remaining model-star equality at `w * zeta`, for every test tensor.
This is an internal reduction condition, not an assumption of the final target. -/
def AdjacentRankBaseModelStarIdentity : Prop :=
  ∀ Ψ : adjacentRankTestSpace ψ σ ℓ,
    Padic.adjacentRankModelIntegral F ψ ν hself σ ℓ χ Ψ
        (weylLong (r + 2) F.Carrier * adjacentRankZeta F.Carrier r) =
      ∫ h, adjacentRankTransformedIntegrand F ψ ν hself σ ℓ χ
        (adjacentRankFullFourier F ψ ν hself σ ℓ Ψ) 1 h
        ∂generalLinearHaar F.Carrier r

private theorem weight_inverseTranspose' {d : ℕ}
    (k : GeneralLinear d F.Carrier) (s : ℂ) :
    determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
        (inverseTranspose d F.Carrier k) s =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) k (-s) := by
  unfold determinantWeight
  change (((normalizedAbsoluteValue F.canonicalTopologicalData)
    (determinant (inverseTranspose d F.Carrier k) : F.Carrier) : ℝ) : ℂ) ^ s = _
  rw [RankOneGammaTwist.determinant_inverseTranspose, Units.val_inv_eq_inv_val, map_inv₀,
    Complex.ofReal_inv, Complex.inv_cpow, Complex.cpow_neg]
  · rfl
  · rw [Complex.arg_ofReal_of_nonneg
      ((normalizedAbsoluteValue F.canonicalTopologicalData).nonneg _)]
    exact Real.pi_ne_zero.symm

private theorem weight_exponent_add' {d : ℕ}
    (k : GeneralLinear d F.Carrier) (s t : ℂ) :
    determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) k (s + t) =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) k s *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) k t :=
  Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
    ((normalizedAbsoluteValue F.canonicalTopologicalData).ne_zero k.det_ne_zero))

/-- Full Fourier covariance extends the base identity to every ambient point,
with exactly the determinant prefactor of the published model-star statement. -/
theorem adjacentRankModelStar_equality_of_base
    (hbase : AdjacentRankBaseModelStarIdentity F ψ ν hself σ ℓ χ)
    (Ψ : adjacentRankTestSpace ψ σ ℓ) (g : GeneralLinear (r + 2) F.Carrier) :
    Padic.adjacentRankModelIntegral F ψ ν hself σ ℓ χ Ψ
        (weylLong (r + 2) F.Carrier * inverseTranspose (r + 2) F.Carrier g) =
      (χ⁻¹ (determinant (adjacentRankZeta F.Carrier r * g)) : ℂ) *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
          (adjacentRankZeta F.Carrier r * g) (((r + 1 : ℕ) : ℂ) / 2) *
        ∫ h, adjacentRankTransformedIntegrand F ψ ν hself σ ℓ χ
          (adjacentRankFullFourier F ψ ν hself σ ℓ Ψ)
          (adjacentRankZeta F.Carrier r * g) h ∂generalLinearHaar F.Carrier r := by
  let k := adjacentRankZeta F.Carrier r * g
  let a₀ := weylLong (r + 2) F.Carrier * adjacentRankZeta F.Carrier r
  have ha : a₀ * inverseTranspose (r + 2) F.Carrier k =
      weylLong (r + 2) F.Carrier * inverseTranspose (r + 2) F.Carrier g := by
    simp only [a₀, k, map_mul, adjacentRankZeta_inverseTranspose, mul_assoc]
    rw [← mul_assoc (adjacentRankZeta F.Carrier r),
      adjacentRankZeta_mul_self, one_mul]
  rw [← ha, Padic.adjacentRankModelIntegral_mul]
  rw [hbase]
  rw [adjacentRankFullFourier_inverseTranspose]
  have hI : (fun h => adjacentRankTransformedIntegrand F ψ ν hself σ ℓ χ
        (determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) k
          ((r + 1 : ℕ) : ℂ) •
          adjacentRankRho0 ψ ν hself σ ℓ k (adjacentRankFullFourier F ψ ν hself σ ℓ Ψ)) 1 h) =
      fun h => determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) k
          ((r + 1 : ℕ) : ℂ) *
        adjacentRankTransformedIntegrand F ψ ν hself σ ℓ χ
          (adjacentRankFullFourier F ψ ν hself σ ℓ Ψ) k h := by
    funext h
    simp only [adjacentRankTransformedIntegrand, adjacentRankRho0_one,
      adjacentRankTestEvaluation_smul]
    ring
  rw [hI, integral_const_mul]
  have hχ : (χ (determinant (inverseTranspose (r + 2) F.Carrier k)) : ℂ) =
      (χ⁻¹ (determinant k) : ℂ) := by
    simp only [RankOneGammaTwist.determinant_inverseTranspose, map_inv]
    rfl
  have hw : determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
        (inverseTranspose (r + 2) F.Carrier k) (((r + 1 : ℕ) : ℂ) / 2) *
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) k
        ((r + 1 : ℕ) : ℂ) =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) k
        (((r + 1 : ℕ) : ℂ) / 2) := by
    rw [weight_inverseTranspose', ← weight_exponent_add']
    congr 1
    ring
  rw [hχ, mul_assoc, ← mul_assoc (determinantWeight _ _ _), hw]
  simp only [mul_assoc]
  rfl

end Langlands.RankinSelberg
