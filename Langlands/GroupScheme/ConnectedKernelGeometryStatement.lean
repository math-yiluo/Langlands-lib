import Langlands.AbelianScheme.GroupScheme
import Langlands.AbelianScheme.Kernel
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # A geometrically connected kernel gives geometrically connected fibers -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every scheme-surjective group-scheme homomorphism with geometrically
connected kernel is geometrically connected. This is a proposition target. -/
def ConnectedKernelHomGeometryStatement : Prop :=
  ∀ (S : Scheme.{u}) (G Q : GroupScheme S) (q : G ⟶ Q),
    Surjective q.hom.hom.left → GeometricallyConnected (kernel q).X.hom →
      GeometricallyConnected q.hom.hom.left

end Langlands.GroupScheme
