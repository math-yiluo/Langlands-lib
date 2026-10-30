import Langlands.AlgebraicGeometry.Picard.RelativePicardZero

/-! # Noetherian models of an abelian scheme over an affine base with two rigidified bundles -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Every abelian scheme `A` over `Spec R`, together with two line bundles `M₁`, `M₂` on its
total space rigidified along the unit section, has a model over a noetherian base: there are a
noetherian commutative ring `R₀` in the same universe, a ring map `φ : R₀ ⟶ R`, an abelian
scheme `A₀` over `Spec R₀` and a morphism `a` from the total space of `A` to that of `A₀` forming
a pullback square over `Spec.map φ` and carrying the unit section of `A` to that of `A₀`,
together with two line bundles `M₁₀`, `M₂₀` on the total space of `A₀`, rigidified along its
unit section, whose underlying line bundles pull back along `a` to those of `M₁` and `M₂`. -/
def AbelianSchemeNoetherianModelStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (A : AbelianScheme (Spec R))
    (M₁ M₂ : RigidifiedLineBundle (unitSection A)),
    ∃ (R₀ : CommRingCat.{u}) (_ : IsNoetherianRing R₀) (φ : R₀ ⟶ R)
      (A₀ : AbelianScheme (Spec R₀)) (a : A.X.left ⟶ A₀.X.left)
      (M₁₀ M₂₀ : RigidifiedLineBundle (unitSection A₀)),
      IsPullback a A.X.hom A₀.X.hom (Spec.map φ) ∧
        unitSection A ≫ a = Spec.map φ ≫ unitSection A₀ ∧
        Nonempty ((LineBundle.pullback a).obj ((RigidifiedLineBundle.forget _).obj M₁₀) ≅
          (RigidifiedLineBundle.forget _).obj M₁) ∧
        Nonempty ((LineBundle.pullback a).obj ((RigidifiedLineBundle.forget _).obj M₂₀) ≅
          (RigidifiedLineBundle.forget _).obj M₂)

end Langlands.AbelianScheme
