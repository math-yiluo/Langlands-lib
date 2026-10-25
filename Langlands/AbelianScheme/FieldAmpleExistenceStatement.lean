import Langlands.AlgebraicGeometry.Picard.Ample
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Existence of ample line bundles over an arbitrary field -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every commutative smooth proper geometrically connected group scheme over
any field admits an actual ample line bundle.
This proposition is a statement target, not a proof. -/
def FieldAmpleExistenceStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : Grp (Over (Spec (CommRingCat.of K)))) [IsCommMonObj G.X],
    Smooth G.X.hom → IsProper G.X.hom → GeometricallyConnected G.X.hom →
      ∃ M : Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left,
        M.IsAmple

end Langlands.GroupScheme
