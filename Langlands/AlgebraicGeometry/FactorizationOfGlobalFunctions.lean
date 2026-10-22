import Mathlib.AlgebraicGeometry.Scheme

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry

/-- Internal factorization criterion using a section, canonical section-ring
isomorphisms on every open, and equality of the underlying point maps. -/
def FactorizationOfGlobalFunctions : Prop :=
  ∀ (X S Y : Scheme.{u}) (p : X ⟶ S) (e : S ⟶ X) (g : X ⟶ Y),
    e ≫ p = 𝟙 S →
    (∀ U : S.Opens, IsIso (p.app U)) →
    (∀ x : X, g x = (e ≫ g) (p x)) →
    g = p ≫ e ≫ g

end Langlands.AlgebraicGeometry
