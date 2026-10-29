import Langlands.AlgebraicGeometry.Picard.LineBundle
import Langlands.AlgebraicGeometry.Picard.PointTangentSeparation
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # A separating line bundle on an abelian group scheme over an algebraically closed field -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every commutative smooth proper geometrically connected group scheme over
an algebraically closed field carries an actual line bundle whose complete
linear system is base-point free on rational points and separates rational
points and nonzero dual-number tangent vectors.
This proposition is a statement target, not a proof. -/
def AlgebraicallyClosedSeparatingLineBundleStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (G : Grp (Over (Spec (CommRingCat.of K)))) [IsCommMonObj G.X],
    Smooth G.X.hom → IsProper G.X.hom → GeometricallyConnected G.X.hom →
      ∃ L : Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left,
        Langlands.AlgebraicGeometry.Picard.SeparatesPointsAndTangents G.X.hom L

end Langlands.GroupScheme
