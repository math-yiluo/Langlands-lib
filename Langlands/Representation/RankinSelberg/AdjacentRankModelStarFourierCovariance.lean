import Langlands.Representation.RankinSelberg.RankOneGammaTwistAlgebra
import Langlands.Representation.RankinSelberg.AdjacentRankModelStarStatement
import Langlands.Representation.RankinSelberg.CharacterChange
import Langlands.HarmonicAnalysis.RectangularRho0FourierCovarianceProof
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof

/-! Fixed-character full Fourier covariance for the adjacent-rank model-star
identity, expressed with the normalized determinant weight. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker TensorProduct GeneralLinear
open scoped NNReal ENNReal Pointwise

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance modelStarFourierTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance modelStarFourierValuative : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance modelStarFourierLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance modelStarFourierT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance modelStarFourierMeasurable : MeasurableSpace F.Carrier := borel _
local instance modelStarFourierBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance modelStarFourierDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance modelStarFourierGLMeasurable (r : ℕ) : MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance modelStarFourierGLBorel (r : ℕ) : BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩

/-- The intrinsic Haar character is the supplied residue-normalized absolute
value on units. This is a consequence of the published scalar scaling law. -/
theorem adjacentRank_distribHaarChar
    (ν : AdditiveHaarMeasure F.Carrier) (a : F.Carrierˣ) :
    (distribHaarChar F.Carrier a : ℝ) =
      normalizedAbsoluteValue F.canonicalTopologicalData (a : F.Carrier) := by
  let T := F.canonicalTopologicalData
  let S : Set F.Carrier := T.Integers
  have hS : MeasurableSet S := T.isOpen_integers.measurableSet
  have h0 : ν.measure S ≠ 0 :=
    ne_of_gt (T.isOpen_integers.measure_pos ν.measure ⟨0, T.Integers.zero_mem⟩)
  have htop : ν.measure S ≠ ∞ := T.isCompact_integers.measure_ne_top
  have hs := congrArg (fun μ : Measure F.Carrier => μ S)
    (padicScalarHaarScaling F T ν.measure a⁻¹)
  change (ν.measure.map (fun x => a⁻¹ • x)) S = _ at hs
  rw [Measure.map_apply (measurable_const_smul _) hS,
    Set.preimage_smul, inv_inv, Measure.smul_apply] at hs
  simp only [map_inv, Units.val_inv_eq_inv_val, inv_inv] at hs
  have he := distribHaarChar_eq_of_measure_smul_eq_mul h0 htop hs
  exact congrArg (fun x : ℝ≥0 => (x : ℝ)) he

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
  (hself : IsSelfDual ψ ν) {r : ℕ}
  (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (ℓ : glFunctionals ψ r σ)

/-- Full plus Fourier transform of the Schwartz factor, keeping the actual
original coefficient factor and its character unchanged. -/
def adjacentRankFullFourier :
    adjacentRankTestSpace ψ σ ℓ →ₗ[ℂ] adjacentRankTestSpace ψ σ ℓ :=
  TensorProduct.map
    (rectangularFourierEquiv ψ ν (r + 1) (r + 2) hself).toLinearMap LinearMap.id

@[simp] theorem adjacentRankFullFourier_tmul
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule) :
    adjacentRankFullFourier F ψ ν hself σ ℓ (Φ ⊗ₜ W) =
      rectangularFourierEquiv ψ ν (r + 1) (r + 2) hself Φ ⊗ₜ W := rfl

/-- Fourier covariance at the inverse transpose, with its scalar expressed
using the same normalized absolute value as the model integral. -/
theorem adjacentRankFullFourier_inverseTranspose
    (k : GeneralLinear (r + 2) F.Carrier) (Ψ : adjacentRankTestSpace ψ σ ℓ) :
    adjacentRankFullFourier F ψ ν hself σ ℓ
        (adjacentRankRho0 ψ ν hself σ ℓ (inverseTranspose (r + 2) F.Carrier k) Ψ) =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) k
          (((r + 1 : ℕ) : ℂ)) •
        adjacentRankRho0 ψ ν hself σ ℓ k
          (adjacentRankFullFourier F ψ ν hself σ ℓ Ψ) := by
  have hc :
      ((((distribHaarChar F.Carrier
          (determinant (inverseTranspose (r + 2) F.Carrier k)) : ℝ) : ℂ) ^
            (r + 1))⁻¹) =
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) k
          (((r + 1 : ℕ) : ℂ)) := by
    rw [RankOneGammaTwist.determinant_inverseTranspose, map_inv, NNReal.coe_inv, Complex.ofReal_inv,
      inv_pow, inv_inv, adjacentRank_distribHaarChar F ν]
    simp only [determinantWeight, Complex.cpow_natCast]
    rfl
  induction Ψ using adjacentRankTestSpace_induction ψ σ ℓ with
  | tmul Φ W =>
    simp only [adjacentRankRho0_tmul, adjacentRankFullFourier_tmul]
    rw [rectangularRho0FourierCovariance ψ ν (r + 1) hself
      (inverseTranspose (r + 2) F.Carrier k) Φ]
    simp only [inverseTranspose_involutive, hc, smul_tmul']
  | add Ψ₁ Ψ₂ h₁ h₂ =>
    simp only [map_add, h₁, h₂, smul_add]

end Langlands.RankinSelberg
