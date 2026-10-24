import Langlands.AlgebraicGeometry.RelativeDifferentialsBaseChange

/-! # Open-immersion locality of relative differentials -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.Scheme

/-- The canonical differential map for a square of open immersions is invertible. -/
def RelativeDifferentialsOpenImmersionIsIsoStatement : Prop :=
  ∀ (X' X S' S : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ S) (f' : X' ⟶ S') (g : X' ⟶ X) (b : S' ⟶ S),
    IsOpenImmersion g → IsOpenImmersion b →
      ∀ (w : g ≫ f = f' ≫ b), IsIso (relativeDifferentialsSquareMap g b w)

end Langlands.Scheme
