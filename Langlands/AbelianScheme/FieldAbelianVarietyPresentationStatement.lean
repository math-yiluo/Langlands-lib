import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Source presentation of abelian group schemes over arbitrary fields -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A commutative smooth proper geometrically connected group scheme over any
field is of finite type, separated, nonempty and geometrically integral.
This proposition is a statement target, not a proof. -/
def FieldAbelianVarietyPresentationStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : Grp (Over (Spec (CommRingCat.of K)))) [IsCommMonObj G.X],
    Smooth G.X.hom → IsProper G.X.hom → GeometricallyConnected G.X.hom →
      LocallyOfFiniteType G.X.hom ∧
      QuasiCompact G.X.hom ∧
      IsSeparated G.X.hom ∧
      Nonempty G.X.left ∧
      GeometricallyIntegral G.X.hom

end Langlands.GroupScheme
