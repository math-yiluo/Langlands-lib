import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.VectorGroupQuotient
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smooth commutative groups of exponent `p` embed into vector groups (Milne 14.49) -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Milne 2017, Proposition 14.49: over a field `k` of characteristic `p > 0`, every smooth
commutative affine group scheme `G` killed by `p` (every point `g` with values in any scheme
over `k` satisfies `g ^ p = 1`) is elementary unipotent: some homomorphism from `G` to a vector
group `𝔾ₐⁿ` is a closed immersion. -/
def SmoothExponentElementaryUnipotentStatement : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [IsCommMonObj G.X],
    (∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X), g ^ p = 1) →
      ∃ (n : ℕ) (e : G ⟶ VectorGroup.groupScheme (CommRingCat.of k) n), IsClosedSubgroup e

end Langlands.GroupScheme
