import Langlands.AlgebraicGeometry.Picard.Ample
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Existence of ample line bundles over an algebraically closed field -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every commutative smooth proper geometrically connected group scheme over
an algebraically closed field admits an actual ample line bundle.
This proposition is a statement target, not a proof. -/
def AlgebraicallyClosedFieldAmpleExistenceStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (G : Grp (Over (Spec (CommRingCat.of K)))) [IsCommMonObj G.X],
    Smooth G.X.hom → IsProper G.X.hom → GeometricallyConnected G.X.hom →
      ∃ M : Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left,
        M.IsAmple

end Langlands.GroupScheme
