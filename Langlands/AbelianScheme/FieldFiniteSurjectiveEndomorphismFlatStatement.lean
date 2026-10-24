import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Flatness of finite surjective abelian endomorphisms over fields -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A finite surjective endomorphism of a commutative smooth proper geometrically
connected group scheme over any field is flat. This is a statement target,
not a proof. -/
def FieldFiniteSurjectiveEndomorphismFlatStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : Grp (Over (Spec (CommRingCat.of K)))) [IsCommMonObj G.X] (f : G ⟶ G),
    Smooth G.X.hom → IsProper G.X.hom → GeometricallyConnected G.X.hom →
      IsFinite f.hom.hom.left → Surjective f.hom.hom.left → Flat f.hom.hom.left

end Langlands.GroupScheme
