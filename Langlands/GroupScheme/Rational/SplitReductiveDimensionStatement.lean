import Langlands.GroupScheme.Rational.RelativeRoots
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.Topology.KrullDimension

/-! # Statement: the dimension of a split reductive group (Milne 21.13) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Dimension of a split reductive group** (Milne, *Algebraic Groups*, Corollary 21.13).
Let `G` be a connected reductive group over a field `k` and `T` a split maximal torus of `G`.
Then the dimension of `G` is the dimension of `T` plus the number of roots of `(G, T)`: the
nonzero characters of `T` with a nonzero weight space in the Lie algebra of `G`. Dimensions are
Krull dimensions of the underlying topological spaces.

This is a statement only; nothing is proved here. -/
def SplitReductiveDimensionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G),
      IsSplitSubtorus t → IsMaximalTorus t →
        topologicalKrullDim G.X.left =
          topologicalKrullDim T.toGrp.X.left + ((relativeRoots t).ncard : WithBot ℕ∞)

end Langlands.GroupScheme
