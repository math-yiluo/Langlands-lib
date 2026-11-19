import Langlands.Representation.Unitary.IntegratedConvolutionStatement
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

universe uG uE

namespace Langlands.Analysis

open MeasureTheory

/-- The integrated action of a norm-preserving representation is multiplicative
for left-measure convolution. -/
theorem integratedActionConvolution : IntegratedActionConvolutionStatement.{uG, uE} := by
  intro G _ _ _ _ E _ _ _ μ _ _ π hπnorm hπmeas f₁ f₂ h₁ h₂
  -- The scalar convolution kernel on the product and the shear `(a, b) ↦ (a, a b)`.
  set K : G × G → ℂ := fun z => f₁ z.1 * f₂ (z.1⁻¹ * z.2) with hKdef
  have hshear : MeasurePreserving (fun z : G × G => (z.1, z.1 * z.2)) (μ.prod μ) (μ.prod μ) :=
    measurePreserving_prod_mul μ μ
  have hemb : MeasurableEmbedding (fun z : G × G => (z.1, z.1 * z.2)) :=
    (MeasurableEquiv.shearMulRight G).measurableEmbedding
  have hKint : Integrable K (μ.prod μ) := by
    rw [← hshear.integrable_comp_emb hemb]
    have hcomp : K ∘ (fun z : G × G => (z.1, z.1 * z.2)) = fun z => f₁ z.1 * f₂ z.2 := by
      funext z
      simp [hKdef]
    rw [hcomp]
    exact h₁.mul_prod h₂
  have hconv : Integrable (fun g => ∫ a, f₁ a * f₂ (a⁻¹ * g) ∂μ) μ :=
    hKint.integral_prod_right
  refine ⟨hconv, ContinuousLinearMap.ext fun x => ?_⟩
  -- The vector kernel on the product.
  have hVint : Integrable (fun z : G × G => K z • π z.2 x) (μ.prod μ) := by
    refine (hKint.norm.mul_const ‖x‖).mono'
      (hKint.aestronglyMeasurable.smul (hπmeas x).comp_snd) ?_
    exact Filter.Eventually.of_forall fun z => by
      rw [norm_smul, hπnorm]
  have hinner : ∀ a : G, ∫ g, K (a, g) • π g x ∂μ =
      f₁ a • π a (∫ b, f₂ b • π b x ∂μ) := by
    intro a
    rw [← integral_mul_left_eq_self (fun g => K (a, g) • π g x) a]
    have hb : ∀ b : G, K (a, a * b) • π (a * b) x = f₁ a • π a (f₂ b • π b x) := by
      intro b
      simp only [hKdef, inv_mul_cancel_left, map_mul, mul_apply_eq_comp,
        map_smul, mul_smul]
    simp_rw [hb]
    rw [integral_smul, ContinuousLinearMap.integral_comp_comm _
      (isometricActionIntegrand_integrable μ π hπnorm hπmeas f₂ h₂ x)]
  simp only [ContinuousLinearMap.comp_apply, integratedIsometricAction_apply]
  calc
    ∫ g, (∫ a, f₁ a * f₂ (a⁻¹ * g) ∂μ) • π g x ∂μ
        = ∫ g, ∫ a, K (a, g) • π g x ∂μ ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
          exact (integral_smul_const (fun a => K (a, g)) (π g x)).symm
    _ = ∫ a, ∫ g, K (a, g) • π g x ∂μ ∂μ :=
          (integral_integral_swap (f := fun a g => K (a, g) • π g x) hVint).symm
    _ = ∫ a, f₁ a • π a (∫ b, f₂ b • π b x ∂μ) ∂μ := by
          simp_rw [hinner]

end Langlands.Analysis
