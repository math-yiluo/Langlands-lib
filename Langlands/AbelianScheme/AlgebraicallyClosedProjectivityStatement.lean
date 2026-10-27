import Langlands.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Projectivity of abelian group schemes over an algebraically closed field -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every commutative smooth proper geometrically connected group scheme over
an algebraically closed field admits a closed immersion into some finite
polynomial-Proj projective space over that field, compatible with the
structure morphisms.
This proposition is a statement target, not a proof. -/
def AlgebraicallyClosedProjectivityStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (G : Grp (Over (Spec (CommRingCat.of K)))) [IsCommMonObj G.X],
    Smooth G.X.hom → IsProper G.X.hom → GeometricallyConnected G.X.hom →
      Langlands.AlgebraicGeometry.IsHProjective G.X.hom

end Langlands.GroupScheme
