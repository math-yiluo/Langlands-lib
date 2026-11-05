import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Derived.Basic

/-! # Derived subgroups of split-torus centralizers in simply connected groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- In a simply connected group `G` over a field `k`, the derived subgroup of the centralizer
`M = Z_G(A)` of a split subtorus `A` is simply connected. -/
def SplitTorusCentralizerDerivedSimplyConnectedStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))), IsSimplyConnected G →
    ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ G), IsSplitSubtorus a →
    ∀ (M : GroupScheme (Spec (CommRingCat.of k))) (j : M ⟶ G),
      (torusCentralizer a).IsRepresentedBy j →
    ∀ (D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ M), IsDerivedSubgroup d →
      IsSimplyConnected D

end Langlands.GroupScheme
