import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Torus.FiniteGaloisSplitMaximal
import Langlands.AlgebraicGeometry.Picard.LineBundle

/-! # Split semisimple groups: simple connectedness and trivial Picard group (statement) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **A split semisimple group is simply connected exactly when its Picard group is zero**
(Milne, *Algebraic Groups* (2017), Proposition 18.19 and Corollary 18.24, specialized to
semisimple groups). For every field `k` and every semisimple group `G` over `k` that has a split
maximal torus, `G` is simply connected if and only if every line bundle on the scheme underlying
`G` is isomorphic to the trivial line bundle.

Line bundles are the Library's locally free rank-one sheaves of modules
(`Langlands.AlgebraicGeometry.Picard.LineBundle`), and `LineBundle.trivial X` is the
structure sheaf. -/
def SplitSemisimpleSimplyConnectedPicardStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsSemisimple G → HasSplitMaximalTorus G →
      (IsSimplyConnected G ↔
        ∀ L : Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left,
          Nonempty (L ≅ Langlands.AlgebraicGeometry.Picard.LineBundle.trivial G.X.left))

end Langlands.GroupScheme
