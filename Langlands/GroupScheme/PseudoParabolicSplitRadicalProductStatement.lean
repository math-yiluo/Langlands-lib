import Langlands.GroupScheme.PseudoParabolic

/-! # The split-radical product description of pseudo-parabolics

The first equality of CGP Proposition 2.2.4, on every relative scheme test.
This is a proposition target and contains no proof or existence claim.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The fppf-local product of a dynamic parabolic with the ground-field
unipotent radical equals its product with the split ground-field radical. -/
def PseudoParabolicSplitRadicalProductStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    ∀ (U V : GroupScheme (Spec (CommRingCat.of k))) (j : U ⟶ G) (n : V ⟶ G),
      IsUnipotentRadical j → IsSplitUnipotentRadical n →
      ∀ (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
        (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
        SubgroupFunctor.FppfLocallyInProduct
          (Dynamic.parabolic χ) (SubgroupFunctor.range j) x ↔
        SubgroupFunctor.FppfLocallyInProduct
          (Dynamic.parabolic χ) (SubgroupFunctor.range n) x

end Langlands.GroupScheme
