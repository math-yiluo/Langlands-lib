import Langlands.AbelianScheme.Kernel
import Langlands.AbelianScheme.Isogeny
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Finite-kernel endomorphisms of abelian group schemes over fields -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- An endomorphism of a commutative smooth proper geometrically connected group
scheme over any field is finite, flat and surjective if its group-scheme kernel
is finite over the field. This is a statement target, not a proof. -/
def FieldFiniteKernelIsogenyStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : Grp (Over (Spec (CommRingCat.of K)))) [IsCommMonObj G.X] (f : G ⟶ G),
    Smooth G.X.hom → IsProper G.X.hom → GeometricallyConnected G.X.hom →
      IsFinite (kernel f).X.hom → IsIsogeny f

end Langlands.GroupScheme
