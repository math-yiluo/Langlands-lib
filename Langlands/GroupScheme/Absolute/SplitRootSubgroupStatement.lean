import Langlands.GroupScheme.MatrixRepresentation.TorusEquivariantAdditive
import Langlands.GroupScheme.Rational.TangentImage
import Langlands.GroupScheme.Torus.Maximal

/-! # Split root subgroups and their Lie lines -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Theorem 21.11(c). For a split maximal torus in a connected reductive
field group, every root subgroup is a closed additive line on all tests. The
torus acts through the root character, and the differential has image the
entire root weight space. A smooth closed subgroup stable under the torus
contains the root subgroup exactly when its Lie image contains that weight
space. -/
def SplitRootSubgroupStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → ∀ (i : T.toGrp ⟶ G), IsMaximalTorus i →
    letI := hG.isAffineHom
    letI := VectorGroup.isAffineHom_groupScheme (CommRingCat.of k) 1
    ∀ α ∈ roots i,
      (∃ x : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G,
        IsClosedSubgroup x ∧ (RelativeRoot.subgroup i α).IsRepresentedBy x ∧
        VectorGroup.IsTorusEquivariant i x α ∧
        LinearMap.range (Lie.targetMapLinear x k) = weightSpace i α) ∧
      (∀ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
        IsClosedSubgroup j → Smooth H.X.hom →
        (AutomorphicAction.conjugation i).IsStable (SubgroupFunctor.range j) →
        (RelativeRoot.subgroup i α ≤ SubgroupFunctor.range j ↔
          weightSpace i α ≤ RelativeRoot.tangentSubmodule (SubgroupFunctor.range j)))

end Langlands.GroupScheme
