import Langlands.GroupScheme.Reductive.Basic

/-!
# Unipotent groups in characteristic zero are connected

Milne, *Algebraic Groups*, Corollary 14.15: the component group of a unipotent algebraic
group has order a power of the characteristic exponent, so a unipotent algebraic group over
a field of characteristic zero is connected.
-/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, *Algebraic Groups*, Corollary 14.15, in characteristic zero: an affine group
scheme locally of finite type over a field `k` of characteristic zero that is unipotent
(`IsUnipotent`: every nonzero finite-dimensional matrix representation has a nonzero fixed
vector) has a connected underlying topological space. -/
def CharZeroUnipotentConnectedStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsAffineHom G.X.hom → LocallyOfFiniteType G.X.hom → IsUnipotent G →
      ConnectedSpace G.X.left

end Langlands.GroupScheme
