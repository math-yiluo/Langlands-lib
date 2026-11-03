import Langlands.GroupScheme.PseudoParabolic
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Absolute.Borel

/-! # A solvable envelope in the absence of proper pseudo-parabolic subgroups

This is a statement extracted from the first branch of the proof of CGP
Theorem C.2.3. No proof of the structural construction is supplied.
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- If a smooth connected affine group over a field has no proper
pseudo-parabolic subgroup, one smooth connected affine solvable closed subgroup
contains every split subtorus by an actual factorization over the field. -/
def NoProperPseudoParabolicSolvableEnvelopeStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [IsAffineHom G.X.hom],
    (∀ (P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G),
      IsPseudoParabolicSubgroup i → IsIso i) →
    ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
      IsClosedSubgroup j ∧
      Smooth H.X.hom ∧ ConnectedSpace H.X.left ∧ IsAffineHom H.X.hom ∧
      IsSolvableGroupScheme H ∧
      ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G),
        IsSplitSubtorus i → ∃ f : S.toGrp ⟶ H, f ≫ j = i

end Langlands.GroupScheme
