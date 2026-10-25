import Langlands.Representation.Hecke.Convolution
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Module.Opposite

/-! # Anti-automorphism pullback on actual Hecke convolution -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace Langlands.Hecke

universe u

open HarmonicAnalysis (SchwartzBruhat)

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [IsMulRightInvariant μ] [IsInvInvariant μ]
  (τ : G ≃ₜ G) (hτmul : ∀ x y, τ (x * y) = τ y * τ x)
  (hτμ : MeasurePreserving τ μ μ)

namespace TestFunction

include hτmul hτμ in
/-- A measure-preserving anti-homeomorphism reverses actual convolution. -/
theorem pullback_convolution (f g : SchwartzBruhat G) :
    pullback τ (convolution μ f g) = convolution μ (pullback τ g) (pullback τ f) := by
  have hτone : τ 1 = 1 := by
    have h := hτmul 1 1
    exact (mul_left_cancel (show τ 1 * 1 = τ 1 * τ 1 by simpa using h)).symm
  have hτinv : ∀ y, τ y⁻¹ = (τ y)⁻¹ := by
    intro y
    symm
    apply inv_eq_of_mul_eq_one_left
    rw [← hτmul, mul_inv_cancel, hτone]
  ext x
  change (∫ y, f y * g (y⁻¹ * τ x) ∂μ) =
    ∫ y, g (τ y) * f (τ (y⁻¹ * x)) ∂μ
  calc
    _ = ∫ u, f (τ u) * g ((τ u)⁻¹ * τ x) ∂μ :=
      (hτμ.integral_comp τ.measurableEmbedding
        (fun y => f y * g (y⁻¹ * τ x))).symm
    _ = ∫ u, f (τ u) * g (τ (x * u⁻¹)) ∂μ := by
      simp_rw [hτmul, hτinv]
    _ = ∫ u, f (τ (u * x)) * g (τ (x * (u * x)⁻¹)) ∂μ :=
      (integral_mul_right_eq_self
        (fun u => f (τ u) * g (τ (x * u⁻¹))) x).symm
    _ = ∫ y, f (τ (y⁻¹ * x)) * g (τ (x * (y⁻¹ * x)⁻¹)) ∂μ :=
      (integral_inv_eq_self
        (fun u => f (τ (u * x)) * g (τ (x * (u * x)⁻¹))) μ).symm
    _ = _ := by simp only [mul_inv_rev, inv_inv, mul_inv_cancel_left, mul_comm (f _)]

end TestFunction

namespace HeckeAlgebra

variable [IsFiniteMeasureOnCompacts μ] [IsMulLeftInvariant μ]

/-- Pullback along an anti-homeomorphism as a complex algebra map to the opposite
of the actual convolution algebra. -/
def antiPullback : HeckeAlgebra μ →ₙₐ[ℂ] (HeckeAlgebra μ)ᵐᵒᵖ where
  toFun f := MulOpposite.op (TestFunction.pullback τ f)
  map_zero' := congrArg MulOpposite.op (map_zero (TestFunction.pullback τ))
  map_add' f g := congrArg MulOpposite.op (map_add (TestFunction.pullback τ) f g)
  map_smul' c f := congrArg MulOpposite.op (map_smul (TestFunction.pullback τ) c f)
  map_mul' f g := congrArg MulOpposite.op
    (TestFunction.pullback_convolution μ τ hτmul hτμ f g)

@[simp] theorem antiPullback_apply (f : HeckeAlgebra μ) (x : G) :
    (antiPullback μ τ hτmul hτμ f).unop x = f (τ x) := rfl

/-- The opposite-algebra map is bijective because homeomorphism pullback is. -/
theorem antiPullback_bijective : Function.Bijective (antiPullback μ τ hτmul hτμ) :=
  MulOpposite.op_bijective.comp (TestFunction.pullback τ).bijective

end HeckeAlgebra

end Langlands.Hecke
