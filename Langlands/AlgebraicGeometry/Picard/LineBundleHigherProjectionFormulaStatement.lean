import Langlands.AlgebraicGeometry.Picard.LineBundle
import Langlands.AlgebraicGeometry.Modules.Tensor
import Langlands.AlgebraicGeometry.Modules.DerivedSections

/-! # Projection formula for higher direct images and an actual line bundle -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- For every scheme morphism `f : X ⟶ Y`, actual line bundle `L` on `Y`, module `M` on `X` and
degree `n`, tensoring the `n`-th higher direct image `Rⁿ f_* M` with `L` agrees, up to
isomorphism, with the `n`-th higher direct image of `f^* L ⊗ M`.
This definition states a proposition and does not prove it. -/
def LineBundleHigherProjectionFormulaStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (L : LineBundle Y) (M : X.Modules) (n : ℕ),
    Nonempty (tensorObj L.obj ((higherDirectImage f n).obj M) ≅
      (higherDirectImage f n).obj (tensorObj ((Scheme.Modules.pullback f).obj L.obj) M))

end Langlands.AlgebraicGeometry.Picard
