import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Statement: smooth morphisms lift along nilpotent thickenings of affine schemes -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- **Infinitesimal lifting for smooth morphisms** (Stacks Project, More on Morphisms,
Definition 37.11.1 (Tag 02H0) and Lemma 37.11.7 (Tag 02H6), extended from first-order to
nilpotent thickenings). Let `f : X ⟶ S` be a smooth morphism of schemes, with `X` not
assumed affine. Let `q : C ⟶ D` be a surjective map of commutative rings with nilpotent
kernel, so that `Spec D ⟶ Spec C` is a thickening of affine schemes. Then every
`S`-morphism `x₀ : Spec D ⟶ X`, where `Spec C` lies over `S` through `s`, extends to an
`S`-morphism `x : Spec C ⟶ X`. -/
def SmoothThickeningLiftingStatement : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] {C D : CommRingCat.{u}} (q : C ⟶ D),
    Function.Surjective q.hom → IsNilpotent (RingHom.ker q.hom) →
      ∀ (x₀ : Spec D ⟶ X) (s : Spec C ⟶ S), x₀ ≫ f = Spec.map q ≫ s →
        ∃ x : Spec C ⟶ X, Spec.map q ≫ x = x₀ ∧ x ≫ f = s

end Langlands.AlgebraicGeometry
