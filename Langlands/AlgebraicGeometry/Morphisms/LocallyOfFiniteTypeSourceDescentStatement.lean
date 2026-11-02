import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Local finite type descends along fppf covers of the source -/

universe u

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

namespace Langlands.AlgebraicGeometry

/-- Local-finite-type branch of Stacks Project Lemma 35.14.3, tag 02KL: if `f` is
surjective, flat and locally of finite presentation and `f ≫ g` is locally of finite
type, then `g` is locally of finite type. The cover `f` is precomposed on the source
of `g`; this is not descent along a base change of the target.
This declaration states the proposition; it supplies no proof of it. -/
def LocallyOfFiniteTypeSourceDescentStatement : Prop :=
  ∀ (X Y S : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ S),
    Surjective f → Flat f → LocallyOfFinitePresentation f →
      LocallyOfFiniteType (f ≫ g) → LocallyOfFiniteType g

end Langlands.AlgebraicGeometry
