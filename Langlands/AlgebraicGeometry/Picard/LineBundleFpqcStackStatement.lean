import Langlands.AlgebraicGeometry.Picard.Groupoid
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Descent.IsStack

/-! # Full fpqc stack descent for actual line bundles: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- The groupoid of actual line bundles is a stack for the fpqc topology on schemes, and for
every morphism `f : X ⟶ S` the relative groupoid `T ↦ PicardGroupoid (T ×_S X)` is a stack for
the fpqc topology induced on the slice category `Over S`. -/
def LineBundleFpqcStackStatement : Prop :=
  PicardGroupoid.pseudofunctor.{u}.IsStack Scheme.fpqcTopology ∧
    ∀ (S X : Scheme.{u}) (f : X ⟶ S),
      (PicardGroupoid.relative f).IsStack (Scheme.fpqcTopology.over S)

end Langlands.AlgebraicGeometry.Picard
