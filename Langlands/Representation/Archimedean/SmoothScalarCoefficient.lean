import Langlands.Representation.Archimedean.SmoothDerivativeFunctional
import Langlands.Representation.Archimedean.SmoothUnitActionDerivative
import Langlands.Geometry.Manifold.LinearLieGroup.Exponential

/-! # Scalar coefficients of Banach smooth-vector actions -/

noncomputable section

open scoped ContDiff Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.DerivativeSmoothVectors

open Langlands.Analysis (hasDerivAt_iff_tendsto_slope_tvs)
open Langlands.LinearLieGroup (expUnit)

universe uB uE

variable {B : Type uB} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
  [FiniteDimensional ℝ B]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (R : Bˣ →* (E →L[ℂ] E))

local notation "I" => 𝓘(ℝ, B)
local notation "D" => DerivativeSmoothVectors I R
local notation "act" => representation I R

/-- Evaluating a genuine smooth orbit by a continuous scalar form gives a smooth function. -/
theorem contMDiff_smoothScalarCoefficient (L : D →L[ℂ] ℂ) (v : D) :
    ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun g => L (act g v)) := by
  obtain ⟨J, S, hS⟩ := smoothDerivativeFunctional I R L
  simp_rw [hS]
  exact (S.restrictScalars ℝ).contMDiff.comp (contMDiff_pi_module_iff.mpr fun w : J =>
    contMDiff_derivativeCoordinates_representation_units R w.val v)

/-- The genuine smooth orbit differentiates against any continuous scalar form along a right
exponential line. -/
theorem hasDerivAt_smoothScalarCoefficient_exp (hR : IsContinuousRepresentation R)
    (L : D →L[ℂ] ℂ) (v : D) (g : Bˣ) (X : B) :
    HasDerivAt (fun t : ℝ => L (act (g * expUnit B (t • X)) v))
      (L (act g (operator I R X v))) 0 := by
  let c (t : ℝ) := (g * expUnit B (t • X)).val
  have hc : HasDerivAt c (g.val * X) 0 := by
    change HasDerivAt (fun t : ℝ => g.val * NormedSpace.exp (t • X)) (g.val * X) 0
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
    exact (h.const_mul g.val).congr_deriv (by simp)
  have hc₀ : c 0 = g.val := by simp [c]
  have h := hasDerivAt_unitsChartOrbit R hR g v hc hc₀
  have hp : (g⁻¹ : Bˣ).val * (g.val * X) = X := by rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [hp] at h
  apply hasDerivAt_iff_tendsto_slope_tvs.mpr
  let L₀ := L.restrictScalars ℝ
  refine ((L₀.continuous.tendsto _).comp (hasDerivAt_iff_tendsto_slope_tvs.mp h)).congr ?_
  intro t
  dsimp only [Function.comp_apply, c, slope_def_module]
  rw [map_smul, map_sub]
  simp only [unitsChartAction_val, L₀, ContinuousLinearMap.coe_restrictScalars']

/-- Continuous forms on genuine smooth vectors give smooth scalar coefficients whose right
exponential derivatives are the genuine derived action. -/
def SmoothScalarCoefficientStatement : Prop :=
  IsContinuousRepresentation R → ∀ (L : D →L[ℂ] ℂ) (v : D),
    ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun g => L (act g v)) ∧
    ∀ (g : Bˣ) (X : B),
      HasDerivAt (fun t : ℝ => L (act (g * expUnit B (t • X)) v)) (L (act g (operator I R X v))) 0

theorem smoothScalarCoefficient : SmoothScalarCoefficientStatement R := by
  intro hR L v
  exact ⟨contMDiff_smoothScalarCoefficient R L v, hasDerivAt_smoothScalarCoefficient_exp R hR L v⟩

end Langlands.Archimedean.DerivativeSmoothVectors
