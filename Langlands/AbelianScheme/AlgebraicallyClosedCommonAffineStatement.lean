import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Common affine neighbourhoods of two closed points of an abelian group scheme -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- In a commutative smooth proper geometrically connected group scheme over
an algebraically closed field, any two closed points lie in a common affine
open subscheme.
This proposition is a statement target, not a proof. -/
def AlgebraicallyClosedCommonAffineStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (G : Grp (Over (Spec (CommRingCat.of K)))) [IsCommMonObj G.X],
    Smooth G.X.hom → IsProper G.X.hom → GeometricallyConnected G.X.hom →
      ∀ x y : G.X.left, IsClosed ({x} : Set G.X.left) → IsClosed ({y} : Set G.X.left) →
        ∃ U : G.X.left.Opens, IsAffineOpen U ∧ x ∈ U ∧ y ∈ U

end Langlands.GroupScheme
