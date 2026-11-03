import Langlands.GroupScheme.PseudoParabolic
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.SplitSolvable

/-! # The split solvable envelope used in minimal pseudo-parabolic conjugacy -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The subgroup `S ⋉ R_us,k(P)` used in CGP C.2.5, expressed as an actual
split solvable representative of the fppf-local product inside `P`. -/
def PseudoParabolicSplitSolvableEnvelopeStatement : Prop :=
  ∀ (k : Type u) [Field k] (G P : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (i : P ⟶ G), IsPseudoParabolicSubgroup i →
      ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (s : S.toGrp ⟶ P),
        IsMaximalSplitTorus s →
          ∀ (U : GroupScheme (Spec (CommRingCat.of k))) (j : U ⟶ P),
            IsSplitUnipotentRadical j →
              ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ P),
                IsSplitSolvableGroupScheme H ∧
                SubgroupFunctor.IsFppfProduct
                  (SubgroupFunctor.range s) (SubgroupFunctor.range j) h

end Langlands.GroupScheme
