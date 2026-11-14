import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Hom.Basic

/-! # Fixed points in an orbit from a quotient Lang equation -/

universe u v w

namespace Langlands.GroupTheory

variable {H : Type u} [Group H] {Q : Type v} [Group Q]
  {X : Type w} [MulAction H X]

/-- Every element is a value of the Lang map `b ↦ b⁻¹ * F b`. -/
def LangSurjective (F : Q → Q) : Prop :=
  ∀ a : Q, ∃ b : Q, b⁻¹ * F b = a

/-- Lift a quotient Lang solution to obtain a fixed point in a supplied orbit.
The kernel of the quotient need only fix the chosen starting point. -/
theorem exists_fixed_in_orbit_of_quotient_lang
    (q : H →* Q) (hq : Function.Surjective q)
    (θ : H → H) (F : Q → Q) (τ : X → X)
    (hcompat : ∀ g : H, q (θ g) = F (q g))
    (hsemi : ∀ (g : H) (x : X), τ (g • x) = θ g • τ x)
    (hlang : LangSurjective F)
    (x₀ : X) (hker : ∀ g : H, q g = 1 → g • x₀ = x₀)
    (h : H) (hx₀ : τ x₀ = h • x₀) :
    ∃ g : H, τ (g • x₀) = g • x₀ := by
  obtain ⟨b, hb⟩ := hlang (q h)⁻¹
  obtain ⟨g, hg⟩ := hq b
  have hk : q (g⁻¹ * θ g * h) = 1 := by
    rw [map_mul, map_mul, map_inv, hcompat, hg, hb, inv_mul_cancel]
  refine ⟨g, ?_⟩
  calc
    τ (g • x₀) = θ g • (h • x₀) := by rw [hsemi, hx₀]
    _ = g • ((g⁻¹ * θ g * h) • x₀) := by
      simp only [smul_smul, ← mul_assoc, mul_inv_cancel, one_mul]
    _ = g • x₀ := by rw [hker _ hk]

end Langlands.GroupTheory
