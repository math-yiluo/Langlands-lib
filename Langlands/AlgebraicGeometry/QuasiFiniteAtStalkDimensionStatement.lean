import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Properties

/-! # Stalk dimension at a quasi-finite point -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- If `f : X ⟶ Y` is locally of finite type and quasi-finite at `x`, then the
Krull dimension of the stalk of `X` at `x` is at most that of the stalk of `Y` at
`f x`. -/
def QuasiFiniteAtStalkDimensionStatement : Prop :=
  ∀ (X Y : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ Y),
    LocallyOfFiniteType f → ∀ (x : X), f.QuasiFiniteAt x →
      ringKrullDim (X.presheaf.stalk x) ≤
        ringKrullDim (Y.presheaf.stalk (f x))

end Langlands.AlgebraicGeometry
