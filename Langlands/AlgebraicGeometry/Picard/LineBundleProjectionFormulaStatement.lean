import Langlands.AlgebraicGeometry.Picard.LineBundle
import Langlands.AlgebraicGeometry.Modules.Tensor

/-! # Projection formula for an actual line bundle -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules

/-- Tensoring a pushforward with an actual line bundle agrees, up to
isomorphism, with pushing forward after tensoring with its actual pullback. -/
def LineBundleProjectionFormulaStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (L : LineBundle Y) (M : X.Modules),
    Nonempty (tensorObj L.obj ((Scheme.Modules.pushforward f).obj M) ≅
      (Scheme.Modules.pushforward f).obj
        (tensorObj ((Scheme.Modules.pullback f).obj L.obj) M))

end Langlands.AlgebraicGeometry.Picard
