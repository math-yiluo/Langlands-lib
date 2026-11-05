import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Rational.RootSubgroup

/-! # Generation of semisimple groups by their actual root subgroups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over an algebraically closed field, a closed subgroup containing every
actual root subgroup for a split maximal torus of a semisimple group has full
range on all test schemes. This is the closed-subgroup formulation of
Milne, Proposition 21.49(a). -/
def SemisimpleRootGenerationStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsSemisimple G),
    letI : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G),
      IsSplitSubtorus t → IsMaximalTorus t →
      ∀ (D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ G),
        IsClosedSubgroup d →
        (∀ α ∈ relativeRoots t,
          RelativeRoot.subgroup t α ≤ SubgroupFunctor.range d) →
        SubgroupFunctor.range d = ⊤

end Langlands.GroupScheme
