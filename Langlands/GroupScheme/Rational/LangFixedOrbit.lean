import Langlands.GroupTheory.LangFixedOrbit
import Langlands.GroupScheme.Torus.FrobeniusConjugate

/-! # Fixed orbits from Lang's theorem on actual geometric group points -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable (k Ω : Type u) [Field k] [Fintype k]
  [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
  {H : Type v} [Group H] {X : Type w} [MulAction H X]

/-- Canonical Frobenius descent on actual geometric points is Lang surjective. -/
theorem langSurjective_descentBasePoint :
    Langlands.GroupTheory.LangSurjective
      (descentBasePoint (algebraBaseMap k Ω)
        (galoisBaseMap k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω))
        (galoisBaseMap_over k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)) G) := by
  intro a
  obtain ⟨b, hb⟩ := exists_eq_inv_mul_descentBasePoint k Ω G a
  exact ⟨b, hb.symm⟩

/-- A semilinear orbit with an equivariant surjection to the actual geometric
points of a smooth connected affine finite-field group has a fixed point,
provided the kernel fixes its starting point. -/
theorem exists_fixed_in_orbit_of_finiteField_quotient
    (q : H →* (Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶
      ((baseChange (algebraBaseMap k Ω)).obj G).X))
    (hq : Function.Surjective q) (θ : H → H) (τ : X → X)
    (hcompat : ∀ g : H, q (θ g) =
      descentBasePoint (algebraBaseMap k Ω)
        (galoisBaseMap k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω))
        (galoisBaseMap_over k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)) G (q g))
    (hsemi : ∀ (g : H) (x : X), τ (g • x) = θ g • τ x)
    (x₀ : X) (hker : ∀ g : H, q g = 1 → g • x₀ = x₀)
    (h : H) (hx₀ : τ x₀ = h • x₀) :
    ∃ g : H, τ (g • x₀) = g • x₀ := by
  exact Langlands.GroupTheory.exists_fixed_in_orbit_of_quotient_lang
    q hq θ _ τ hcompat hsemi (langSurjective_descentBasePoint k Ω G) x₀ hker h hx₀

end Langlands.GroupScheme
