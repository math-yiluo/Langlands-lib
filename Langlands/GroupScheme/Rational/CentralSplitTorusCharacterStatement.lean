import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Reductive.Basic

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over every field `k`, every nonzero rational character `χ ∈ X^*(G)_k` of a connected reductive
 group `G` restricts to a nonzero character of some central split torus `i : A ⟶ G`. -/
def CentralSplitTorusCharacterStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))), IsConnectedReductive G →
    ∀ χ : rationalCharacters G, χ ≠ 0 →
      ∃ (A : CommGroupScheme (Spec (CommRingCat.of k))) (i : A.toGrp ⟶ G),
        IsCentralSplitTorus i ∧ characterRestrict i χ ≠ 0

end Langlands.GroupScheme
