import Langlands.Representation.Unitary.IntegratedOperator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-! # Symmetry of integrated isometric actions with star-invariant weights -/

noncomputable section

open MeasureTheory Langlands.Analysis
open scoped InnerProductSpace ComplexConjugate

namespace Langlands.TraceFormula

universe uG uH

variable {G : Type uG} [Group G] [MeasurableSpace G] [MeasurableInv G]
  {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure G) [μ.IsInvInvariant] (π : G →* (H →L[ℂ] H))
  (hn : ∀ (g : G) (x : H), ‖π g x‖ = ‖x‖)
  (hm : ∀ x : H, AEStronglyMeasurable (fun g => π g x) μ)

omit [MeasurableSpace G] [MeasurableInv G] [CompleteSpace H] in
include hn in
/-- An isometric representation moves inner products by the inverse element. -/
theorem inner_map_inv_eq (g : G) (x y : H) : ⟪x, π g⁻¹ y⟫_ℂ = ⟪π g x, y⟫_ℂ := by
  let e : H →ₗᵢ[ℂ] H := ⟨(π g).toLinearMap, hn g⟩
  have h : π g (π g⁻¹ y) = y := by
    change (π g * π g⁻¹) y = y
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  calc ⟪x, π g⁻¹ y⟫_ℂ = ⟪e x, e (π g⁻¹ y)⟫_ℂ := (e.inner_map_map x _).symm
    _ = ⟪π g x, y⟫_ℂ := by
      change ⟪π g x, π g (π g⁻¹ y)⟫_ℂ = _
      rw [h]

/-- The integrated action of a weight with `f (g⁻¹) = conj (f g)` for an isometric
representation and an inversion-invariant measure is symmetric. -/
theorem integratedIsometricAction_isSymmetric (f : G → ℂ) (hf : Integrable f μ)
    (hstar : ∀ g, f g⁻¹ = conj (f g)) :
    (integratedIsometricAction μ π hn hm f hf).IsSymmetric := by
  intro x y
  have hx := isometricActionIntegrand_integrable μ π hn hm f hf x
  have hy := isometricActionIntegrand_integrable μ π hn hm f hf y
  change ⟪∫ g, f g • π g x ∂μ, y⟫_ℂ = ⟪x, ∫ g, f g • π g y ∂μ⟫_ℂ
  rw [← inner_conj_symm, ← integral_inner hx y, ← integral_inner hy x, ← integral_conj]
  have hinv := MeasureTheory.integral_inv_eq_self
    (fun g => ⟪x, f g • π g y⟫_ℂ) μ
  rw [← hinv]
  congr 1
  funext g
  rw [inner_smul_right, inner_smul_right, hstar, inner_map_inv_eq π hn g x y, map_mul,
    inner_conj_symm]

/-- For an isometric representation of a group on a complex Hilbert space and an
inversion-invariant measure, the integrated action of an integrable weight `f` with
`f (g⁻¹) = conj (f g)` is a symmetric operator. -/
def SymmetricIntegratedActionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [MeasurableSpace G] [MeasurableInv G]
    (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (μ : Measure G) [μ.IsInvInvariant] (π : G →* (H →L[ℂ] H))
    (hn : ∀ (g : G) (x : H), ‖π g x‖ = ‖x‖)
    (hm : ∀ x : H, AEStronglyMeasurable (fun g => π g x) μ)
    (f : G → ℂ) (hf : Integrable f μ),
    (∀ g, f g⁻¹ = conj (f g)) → (integratedIsometricAction μ π hn hm f hf).IsSymmetric

theorem symmetricIntegratedAction : SymmetricIntegratedActionStatement.{uG, uH} :=
  fun _ _ _ _ _ _ _ _ μ _ π hn hm f hf hstar =>
    integratedIsometricAction_isSymmetric μ π hn hm f hf hstar

end Langlands.TraceFormula
