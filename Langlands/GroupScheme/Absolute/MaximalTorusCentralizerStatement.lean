import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Torus.Maximal

/-! # Statement: a maximal torus of a connected reductive group is its own centralizer -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Maximal tori are self-centralizing** (Milne, Corollary 17.84, the "only if" direction).
Let `G` be a connected reductive group over a field `k` and `j : T ⟶ G` a maximal torus. Then
the centralizer of `T` in `G` is `T`: on every test scheme `U` over `Spec k`, a point of `G`
over `U` commutes with all points of `T` over all `U`-schemes exactly when it is the image of
a point of `T` over `U`. -/
def MaximalTorusCentralizerStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
      IsMaximalTorus j → torusCentralizer j = SubgroupFunctor.range j

end Langlands.GroupScheme
