import Langlands.Representation.GodementJacquet.Zeta
import Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
import Langlands.Representation.Smooth.SmallRealizationProof
import Mathlib.MeasureTheory.Group.Prod

/-!
# Left averaging inside full-matrix integrals

A generic Fubini computation: averaging the second factor of an integrand on the
left over a set of finite measure, on which the first factor is left invariant,
multiplies the integral by the measure of that set.
-/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory

universe uG

section LeftAverage

variable {G : Type uG} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]

/-- Left averaging over `Ω` against a weight `a` that is left invariant under `Ω`.
Both integrability and the value follow from integrability of `a * W`. -/
theorem leftAverage_integral (Ω : Set G) (hΩm : MeasurableSet Ω) (hΩ : μ Ω ≠ ⊤)
    (a W : G → ℂ) (ha : ∀ x ∈ Ω, ∀ g, a (x * g) = a g)
    (haW : Integrable (fun g => a g * W g) μ) :
    Integrable (fun g => a g * ∫ x in Ω, W (x * g) ∂μ) μ ∧
      ∫ g, a g * (∫ x in Ω, W (x * g) ∂μ) ∂μ = (μ.real Ω : ℂ) * ∫ g, a g * W g ∂μ := by
  set ν := μ.restrict Ω with hνdef
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hΩ
  have hshear : MeasurePreserving (fun z : G × G => (z.1, z.1 * z.2)) (ν.prod μ) (ν.prod μ) :=
    measurePreserving_prod_mul ν μ
  let H : G × G → ℂ := fun z => a (z.1⁻¹ * z.2) * W z.2
  let P : G × G → ℂ := fun z => (fun _ : G => (1 : ℂ)) z.1 * (fun g => a g * W g) z.2
  have hP : Integrable P (ν.prod μ) := (integrable_const (1 : ℂ)).mul_prod haW
  have hae : ∀ᵐ z ∂(ν.prod μ), z.1 ∈ Ω :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hΩm)
  have hHP : P =ᵐ[ν.prod μ] H := by
    filter_upwards [hae] with z hz
    have h := ha z.1 hz (z.1⁻¹ * z.2)
    rw [mul_inv_cancel_left] at h
    simp only [P, H, one_mul, h]
  have hH : Integrable H (ν.prod μ) := hP.congr hHP
  let F : G × G → ℂ := fun z => a z.2 * W (z.1 * z.2)
  have hF_eq : F = H ∘ (fun z : G × G => (z.1, z.1 * z.2)) := by
    funext z
    simp only [F, H, Function.comp_apply, inv_mul_cancel_left]
  have hF : Integrable F (ν.prod μ) := by
    rw [hF_eq]
    exact hshear.integrable_comp_of_integrable hH
  have hpoint : (fun g => a g * ∫ x in Ω, W (x * g) ∂μ) = fun g => ∫ x, F (x, g) ∂ν := by
    funext g
    simp only [F, ν]
    rw [integral_const_mul]
  refine ⟨?_, ?_⟩
  · rw [hpoint]
    exact hF.integral_prod_right
  · calc
      ∫ g, a g * (∫ x in Ω, W (x * g) ∂μ) ∂μ = ∫ g, ∫ x, F (x, g) ∂ν ∂μ := by
        rw [hpoint]
      _ = ∫ z, F z ∂(ν.prod μ) := (integral_prod_symm F hF).symm
      _ = ∫ z, H z ∂(ν.prod μ) := by
        rw [hF_eq]
        exact hshear.integral_comp (MeasurableEquiv.shearMulRight G).measurableEmbedding H
      _ = ∫ z, P z ∂(ν.prod μ) := integral_congr_ae hHP.symm
      _ = (∫ _x, (1 : ℂ) ∂ν) * ∫ g, a g * W g ∂μ :=
        integral_prod_mul (μ := ν) (ν := μ) (fun _ : G => (1 : ℂ)) (fun g => a g * W g)
      _ = (μ.real Ω : ℂ) * ∫ g, a g * W g ∂μ := by
        simp [ν, integral_const]

end LeftAverage

end Langlands.GodementJacquet
