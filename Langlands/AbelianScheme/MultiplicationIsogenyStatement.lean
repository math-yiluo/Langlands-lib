import Langlands.AbelianScheme.Multiplication
import Langlands.AbelianScheme.Isogeny
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Nonzero integer multiplication on abelian schemes -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Nonzero integer multiplication is finite, flat and surjective on a
commutative group scheme whose structure map is smooth, proper and
geometrically connected. This is a statement target, not a proof. -/
def MultiplicationIsogenyStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : Grp (Over S)) [IsCommMonObj G.X],
    Smooth G.X.hom → IsProper G.X.hom → GeometricallyConnected G.X.hom →
      ∀ (n : ℤ), n ≠ 0 → IsIsogeny (multiplication G n)

end Langlands.GroupScheme
