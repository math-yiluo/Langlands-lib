import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.GeometricComponents

/-! # The component group of a unipotent group (Milne 14.15) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Corollary 14.15: if an affine algebraic group `G` over a field `k` of
characteristic exponent `p` is unipotent, then the order of `π₀(G)`, the number of connected
components of `G` after base change to an algebraic closure of `k`, is a power of `p`. -/
def UnipotentComponentOrderStatement : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [ExpChar k p]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom],
    IsUnipotent G → ∃ n : ℕ, Nat.card (IdentityComponent.GeometricComponents k G) = p ^ n

end Langlands.GroupScheme
