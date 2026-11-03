import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.Lattice

/-! # Connected reductive groups over infinite fields are dominated by a torus -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over an infinite field `k`, every connected reductive group scheme `G` admits a torus `T`
over `k` and a morphism of `k`-schemes `T → G`, not necessarily a homomorphism, whose image
is Zariski dense in `G`. -/
def ReductiveTorusDominationStatement : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∃ (T : GroupScheme (Spec (CommRingCat.of k))) (f : T.X ⟶ G.X),
      IsTorus T ∧ Dense (Set.range f.left)

end Langlands.GroupScheme
