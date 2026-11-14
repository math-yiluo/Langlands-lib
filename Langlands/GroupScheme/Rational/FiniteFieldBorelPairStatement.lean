import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.GroupScheme.Torus.Maximal

/-! # Statement: Borel pairs of connected group varieties over finite fields -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Proposition 17.99. Let `G` be a smooth connected affine group over a finite field
`k`. A Borel pair of `G` is a geometric Borel subgroup `b : B ⟶ G` together with a maximal
torus `j : T ⟶ G` contained in it.
* `G` has a Borel pair.
* Any two Borel pairs of `G` are conjugate by a `k`-point of `G`. -/
def FiniteFieldBorelPairStatement : Prop :=
  ∀ (k : Type u) [Field k] [Finite k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    (∃ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G)
        (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
        IsGeometricBorelSubgroup b ∧ IsMaximalTorus j ∧
          SubgroupFunctor.range j ≤ SubgroupFunctor.range b) ∧
    ∀ (B B' : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G) (b' : B' ⟶ G)
      (T T' : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G)
      (j' : T'.toGrp ⟶ G),
      IsGeometricBorelSubgroup b → IsMaximalTorus j →
      SubgroupFunctor.range j ≤ SubgroupFunctor.range b →
      IsGeometricBorelSubgroup b' → IsMaximalTorus j' →
      SubgroupFunctor.range j' ≤ SubgroupFunctor.range b' →
        ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
          SubgroupFunctor.range (b ≫ (G.innerIso g).hom) = SubgroupFunctor.range b' ∧
            SubgroupFunctor.range (j ≫ (G.innerIso g).hom) = SubgroupFunctor.range j'

end Langlands.GroupScheme
