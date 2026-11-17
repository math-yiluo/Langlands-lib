import Langlands.GroupScheme.VectorGroupQuotient
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.Perfect

/-! # Smooth connected commutative groups of exponent `p` over perfect fields (Milne 14.54) -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Milne 2017, Proposition 14.54: over a perfect field `k` of characteristic `p > 0`, every
smooth connected commutative affine group scheme `G` killed by `p` (every point `g` with values
in any scheme over `k` satisfies `g ^ p = 1`) is isomorphic to a vector group `𝔾ₐʳ`. -/
def PerfectFieldExponentVectorGroupStatement : Prop :=
  ∀ (k : Type u) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [IsCommMonObj G.X],
    ConnectedSpace G.X.left →
      (∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X), g ^ p = 1) →
        ∃ r : ℕ, Nonempty (G ≅ VectorGroup.groupScheme (CommRingCat.of k) r)

end Langlands.GroupScheme
