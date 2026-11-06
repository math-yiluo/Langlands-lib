import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry

/-- A ring pullback with one surjective map induces a pushout in schemes. -/
def AffineSchemePushoutStatement : Prop :=
  ∀ (A B C D : CommRingCat.{u}) (f : B ⟶ D) (g : C ⟶ D)
    (i : A ⟶ B) (j : A ⟶ C),
    Function.Surjective f.hom →
      IsPullback i j f g →
        IsPushout (Spec.map f) (Spec.map g) (Spec.map i) (Spec.map j)

end Langlands.AlgebraicGeometry
