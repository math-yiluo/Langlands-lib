import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Torus.FiniteGaloisSplitMaximal

/-! # Factoriality of the coordinate ring of a split simply connected group (statement) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **The coordinate ring of a split simply connected semisimple group is factorial**
(Popov 1974, Proposition 1 and its Corollary; over an arbitrary field for split groups, via
Milne, *Algebraic Groups* (2017), Corollary 18.24). For every field `k` and every simply
connected group `G` over `k` with a split maximal torus, the ring of global sections of the
scheme underlying `G` is an integral domain with unique factorization. -/
def SplitSimplyConnectedFactorialStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsSimplyConnected G → HasSplitMaximalTorus G →
      IsDomain Γ(G.X.left, ⊤) ∧ UniqueFactorizationMonoid Γ(G.X.left, ⊤)

end Langlands.GroupScheme
