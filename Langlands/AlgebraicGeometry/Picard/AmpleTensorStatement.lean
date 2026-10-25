import Langlands.AlgebraicGeometry.Picard.Ample

/-!
# Ampleness of a tensor product of actual line bundles

The target permits any line bundle whose underlying module sheaf is isomorphic
to the genuine tensor product. Its proof is a separate obligation.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- A line bundle representing the actual tensor product of two ample line
bundles is ample. -/
def AmpleTensorStatement : Prop :=
  ∀ (X : Scheme.{u}) (L M N : LineBundle X),
    Nonempty (Langlands.Scheme.Modules.tensorObj L.obj M.obj ≅ N.obj) →
      L.IsAmple → M.IsAmple → N.IsAmple

end Langlands.AlgebraicGeometry.Picard
