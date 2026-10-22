import Langlands.AbelianScheme.Multiplication
import Langlands.AbelianScheme.Isogeny
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Positive multiplication on abelian group schemes over fields -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Positive-natural multiplication is finite, flat and surjective on a
commutative smooth proper geometrically connected group scheme over any field.
This is a statement target, not a proof. -/
def FieldMultiplicationIsogenyStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : Grp (Over (Spec (CommRingCat.of K)))) [IsCommMonObj G.X],
    Smooth G.X.hom → IsProper G.X.hom → GeometricallyConnected G.X.hom →
      ∀ (n : ℕ), 0 < n → IsIsogeny (multiplication G (n : ℤ))

end Langlands.GroupScheme
