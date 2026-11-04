import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Finite group schemes over a field are killed by a positive integer -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every group scheme over a field whose structure morphism is finite has one
positive exponent that kills every point on every scheme over the base field.
This is the existence form of Milne 2017, Proposition 11.32. This proposition is
a statement target, not a proof. -/
def FiniteGroupSchemeUniformExponentStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsFinite G.X.hom →
    ∃ n : ℕ, 0 < n ∧ ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X), x ^ n = 1

end Langlands.GroupScheme
