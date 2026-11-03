import Langlands.GroupScheme.Rational.MinimalPseudoParabolic
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Rational.TorusCentralizer

/-! # Maximal split tori and the minimality criterion for pseudo-parabolics -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- CGP Proposition C.2.4 and the maximality observation immediately preceding
it, expressed through actual embeddings and represented fppf-local products. -/
def PseudoParabolicMaximalSplitTorusStructureStatement : Prop :=
  ∀ (k : Type u) [Field k] (G P : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (i : P ⟶ G), IsPseudoParabolicSubgroup i →
      ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (s : S.toGrp ⟶ P),
        IsMaximalSplitTorus s →
          IsMaximalSplitTorus (s ≫ i) ∧
          torusCentralizer (s ≫ i) ≤ SubgroupFunctor.range i ∧
          ∀ (U : GroupScheme (Spec (CommRingCat.of k))) (j : U ⟶ P),
            IsSplitUnipotentRadical j →
              (IsMinimalPseudoParabolicSubgroup i ↔
                SubgroupFunctor.IsFppfProduct (torusCentralizer (s ≫ i))
                  (SubgroupFunctor.range (j ≫ i)) i)

end Langlands.GroupScheme
