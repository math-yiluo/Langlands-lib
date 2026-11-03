import Langlands.GroupScheme.Absolute.Borel

/-! # Statement: a parabolic subgroup contains a maximal torus of the ambient group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Maximal tori in parabolic subgroups** (Milne, Theorem 25.1, converse proof,
with Theorem 17.82 and Corollary 17.83). A parabolic subgroup of a connected
reductive group over a field contains a torus defined over that field which is
maximal in the ambient group. -/
def ParabolicMaximalTorusStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
      ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G),
        IsParabolicSubgroup i →
          ∃ (T : CommGroupScheme (Spec (CommRingCat.of k)))
            (j : T.toGrp ⟶ G) (f : T.toGrp ⟶ P),
            IsMaximalTorus j ∧ f ≫ i = j

end Langlands.GroupScheme
