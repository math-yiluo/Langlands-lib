import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.Torus.Weights
import Langlands.GroupScheme.Reductive.Basic

/-! # Borel–Tits 7.2: a split reductive subgroup through a maximal split torus -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Borel–Tits (1965), Théorème 7.2, existence part.** Over every field `k`, let `G` be
connected reductive and let `i : S ⟶ G` be a maximal split torus. There is a closed connected
reductive subgroup `j : F ⟶ G` and a factorization `f ≫ j = i` such that `f` is a maximal torus
of `F` and the roots of `f` in `F` are exactly the nonmultipliable relative roots of `i`, the
roots `a` of `i` with `2 • a` not a root of `i`. -/
def MaximalSplitSubgroupStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (S : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : S.toGrp ⟶ G), IsMaximalSplitTorus i →
      ∃ (F : GroupScheme (Spec (CommRingCat.of k))) (hF : IsConnectedReductive F)
        (j : F ⟶ G) (f : S.toGrp ⟶ F),
        IsClosedSubgroup j ∧ f ≫ j = i ∧ IsMaximalTorus f ∧
          (haveI := hG.isAffineHom
           haveI := hF.isAffineHom
           roots f = {a | a ∈ roots i ∧ (2 : ℤ) • a ∉ roots i})

end Langlands.GroupScheme
