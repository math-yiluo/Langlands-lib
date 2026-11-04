import Langlands.GroupScheme.PseudoParabolic

/-! # Split radical containment for pseudo-parabolic subgroups

The first containment in the proof of CGP Corollary 2.2.5, expressed through
the two factors on every relative scheme test. This module states a proposition
and supplies no proof or existence theorem.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- For `P = P_G(χ) R_{u,k}(G)`, both `U_G(χ)` and `R_{us,k}(G)` lie in
`R_{us,k}(P)`, viewed inside `G`, on every relative scheme test. -/
def PseudoParabolicSplitRadicalContainmentStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    ∀ (R : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ G), IsUnipotentRadical r →
    ∀ (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      (P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G),
      (Dynamic.parabolic χ).IsFppfProduct (SubgroupFunctor.range r) i →
      ∀ (V W : GroupScheme (Spec (CommRingCat.of k))) (n : V ⟶ G) (m : W ⟶ P),
        IsSplitUnipotentRadical n → IsSplitUnipotentRadical m →
          Dynamic.unipotent χ ≤ SubgroupFunctor.range (m ≫ i) ∧
            SubgroupFunctor.range n ≤ SubgroupFunctor.range (m ≫ i)

end Langlands.GroupScheme
