import Langlands.Representation.RankinSelberg.AdjacentRankModelStarStatement
import Langlands.Representation.RankinSelberg.AdjacentRankModelConvergenceProof

/-! Compact support and integrability for the expanded transformed coefficient
in the fixed-Fourier-action adjacent-rank model-star formula. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker TensorProduct GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Compact support for the actual Weyl/inverse-transpose coefficient, without
changing any Fourier action or imposing a topology on the carrier. -/
theorem adjacentRankTransformedPure_hasCompactSupport
    (ψ : UnitaryAdditiveCharacter F.Carrier) (r : ℕ)
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule) :
    HasCompactSupport (fun h : GeneralLinear (r + 1) F.Carrier =>
      Φ (adjacentRankKernelMatrix h) *
        glModelFunction ψ r σ ℓ W
          (weylLong (r + 1) F.Carrier * inverseTranspose (r + 1) F.Carrier h⁻¹)) := by
  obtain ⟨v, hv⟩ := W.property
  let ℓ' : glFunctionals (ψ.scale (-1)) r (inverseTransposePullback σ) :=
    ⟨(dualFunctional ψ σ ℓ).val, by
      simpa only [glFunctionals, glInverseFunctionals, standardCharacter_scale_neg_one] using
        (dualFunctional ψ σ ℓ).property⟩
  have he (a : GeneralLinear (r + 1) F.Carrier) :
      glModelFunction ψ r σ ℓ W
          (weylLong (r + 1) F.Carrier * inverseTranspose (r + 1) F.Carrier a) =
        glModelFunction (ψ.scale (-1)) r (inverseTransposePullback σ) ℓ'
          (modelMap (inverseTransposePullback σ) ℓ' v) a := by
    change W.val.val _ = _
    rw [← hv]
    change ℓ.val (σ (weylLong (r + 1) F.Carrier *
      inverseTranspose (r + 1) F.Carrier a) v) =
        ℓ.val (σ (weylLong (r + 1) F.Carrier)
          (σ (inverseTranspose (r + 1) F.Carrier a) v))
    rw [map_mul, Module.End.mul_apply]
  simpa only [he] using
    adjacentRankPure_hasCompactSupport F (ψ.scale (-1)) r
      (inverseTransposePullback σ) (inverseTransposePullback_isSmooth σ hσ)
      ℓ' Φ (modelMap (inverseTransposePullback σ) ℓ' v)

local instance : MeasurableSpace F.Carrier := borel _
local instance : BorelSpace F.Carrier := ⟨rfl⟩
local instance : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance (r : ℕ) : MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance (r : ℕ) : BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩

/-- The fixed-action integrand with its transformed coefficient argument
expanded. The input tensor may already have had its Schwartz factor Fourier
transformed; this definition performs no coefficient-space identification. -/
def adjacentRankTransformedIntegrand
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ ν) {r : ℕ}
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F.Carrier)
    (Ψ : adjacentRankTestSpace ψ σ ℓ) (k : GeneralLinear (r + 2) F.Carrier)
    (h : GeneralLinear (r + 1) F.Carrier) : ℂ :=
  adjacentRankTestEvaluation ψ σ ℓ (adjacentRankRho0 ψ ν hself σ ℓ k Ψ)
    (adjacentRankKernelMatrix h)
    (weylLong (r + 1) F.Carrier * inverseTranspose (r + 1) F.Carrier h⁻¹) *
    (χ⁻¹ (determinant h) : ℂ) *
    determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) h ((r : ℂ) / 2)

/-- Every test tensor has an integrable expanded transformed-coefficient
integrand, with the Fourier action still at the supplied character `ψ`. -/
theorem adjacentRankTransformed_integrable_of_isSmooth
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ ν) (r : ℕ)
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F.Carrier)
    (Ψ : adjacentRankTestSpace ψ σ ℓ) (k : GeneralLinear (r + 2) F.Carrier) :
    Integrable (adjacentRankTransformedIntegrand F ψ ν hself σ ℓ χ Ψ k)
      (generalLinearHaar F.Carrier r) := by
  unfold adjacentRankTransformedIntegrand
  induction Ψ using adjacentRankTestSpace_induction ψ σ ℓ with
  | tmul Φ W =>
    let Φ' := rectangularRho0 ψ ν (r + 1) hself k Φ
    change Integrable (fun h : GeneralLinear (r + 1) F.Carrier =>
      Φ' (adjacentRankKernelMatrix h) *
        glModelFunction ψ r σ ℓ W
          (weylLong (r + 1) F.Carrier * inverseTranspose (r + 1) F.Carrier h⁻¹) *
        (χ⁻¹ (determinant h) : ℂ) *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) h ((r : ℂ) / 2))
      (generalLinearHaar F.Carrier r)
    apply Continuous.integrable_of_hasCompactSupport
    · have hχ : Continuous fun h : GeneralLinear (r + 1) F.Carrier =>
          (χ⁻¹ (determinant h) : ℂ) :=
        Units.continuous_val.comp ((χ⁻¹).continuous.comp determinantContinuous.continuous)
      have harg : Continuous fun h : GeneralLinear (r + 1) F.Carrier =>
          weylLong (r + 1) F.Carrier * inverseTranspose (r + 1) F.Carrier h⁻¹ :=
        continuous_const.mul ((continuous_inverseTranspose _ _).comp continuous_inv)
      exact ((((SchwartzBruhat.continuous Φ').comp
        (continuous_adjacentRankKernelMatrix F r)).mul
          ((glModelFunction_continuous ψ r σ hσ ℓ W).comp harg)).mul hχ).mul
            (continuous_adjacentRank_determinantWeight F _ _)
    · exact ((adjacentRankTransformedPure_hasCompactSupport F ψ r σ hσ ℓ Φ' W).mul_right).mul_right
  | add Ψ₁ Ψ₂ h₁ h₂ =>
    have he : (fun h : GeneralLinear (r + 1) F.Carrier =>
        adjacentRankTestEvaluation ψ σ ℓ
          (adjacentRankRho0 ψ ν hself σ ℓ k (Ψ₁ + Ψ₂))
          (adjacentRankKernelMatrix h)
          (weylLong (r + 1) F.Carrier * inverseTranspose (r + 1) F.Carrier h⁻¹) *
          (χ⁻¹ (determinant h) : ℂ) *
          determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) h ((r : ℂ) / 2)) =
        (fun h =>
          adjacentRankTestEvaluation ψ σ ℓ (adjacentRankRho0 ψ ν hself σ ℓ k Ψ₁)
            (adjacentRankKernelMatrix h)
            (weylLong (r + 1) F.Carrier * inverseTranspose (r + 1) F.Carrier h⁻¹) *
            (χ⁻¹ (determinant h) : ℂ) *
            determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) h ((r : ℂ) / 2)) +
        (fun h =>
          adjacentRankTestEvaluation ψ σ ℓ (adjacentRankRho0 ψ ν hself σ ℓ k Ψ₂)
            (adjacentRankKernelMatrix h)
            (weylLong (r + 1) F.Carrier * inverseTranspose (r + 1) F.Carrier h⁻¹) *
            (χ⁻¹ (determinant h) : ℂ) *
            determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) h ((r : ℂ) / 2)) := by
      funext h
      simp only [map_add, adjacentRankTestEvaluation_add, Pi.add_apply, add_mul]
    rw [he]
    exact h₁.add h₂

end Langlands.RankinSelberg
