import Langlands.AlgebraicGeometry.Picard.Ample

/-!
# Ampleness under an actual module-sheaf isomorphism

This proposition states invariance of the published ampleness predicate under
every isomorphism of the underlying module sheaves. Its proof is separate.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- An actual module-sheaf isomorphism transports ampleness between line bundles. -/
def AmpleIsoStatement : Prop :=
  ∀ (X : Scheme.{u}) (L M : LineBundle X),
    Nonempty (L.obj ≅ M.obj) → L.IsAmple → M.IsAmple

end Langlands.AlgebraicGeometry.Picard
