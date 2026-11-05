import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Rational.RootSubgroup

/-! # Root subgroups relative to a smooth connected normal subgroup -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every root subgroup for a split maximal torus of a semisimple group over
an algebraically closed field is either contained in a given smooth connected
normal closed subgroup or centralizes that entire subgroup on every refinement.
This isolates the root-level step in Milne's rewritten proof of 21.51. -/
def SemisimpleNormalRootDichotomyStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsSemisimple G),
    letI : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G),
      IsSplitSubtorus t → IsMaximalTorus t →
      ∀ (H : GroupScheme (Spec (CommRingCat.of k)))
        [Smooth H.X.hom] [ConnectedSpace H.X.left] (h : H ⟶ G),
        IsClosedSubgroup h → (SubgroupFunctor.range h).IsNormal →
        ∀ α ∈ relativeRoots t,
          RelativeRoot.subgroup t α ≤ SubgroupFunctor.range h ∨
          RelativeRoot.subgroup t α ≤
            (AutomorphicAction.conjugation h).fixedSubgroup

end Langlands.GroupScheme
