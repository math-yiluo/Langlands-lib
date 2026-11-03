import Langlands.GroupScheme.PseudoComplete
import Langlands.GroupScheme.Reductive.UnipotentRadical
import Langlands.GroupScheme.SubgroupFunctor.FppfProduct
import Langlands.GroupScheme.PseudoParabolic
import Langlands.GroupScheme.HomogeneousQuotientStatement

/-! # Pseudo-completeness of pseudo-parabolic quotients

This module states CGP Proposition C.1.6 for any supplied actual homogeneous
quotient with the published all-test right-coset fibers. It supplies no proof.
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Any supplied homogeneous quotient of a smooth connected affine group over
an arbitrary field by a pseudo-parabolic subgroup is pseudo-complete.
The ambient geometric hypotheses are fields of `IsPseudoParabolicSubgroup`. -/
def PseudoParabolicQuotientPseudoCompleteStatement : Prop :=
  ∀ (k : Type u) [Field k] (G P : GroupScheme (Spec (CommRingCat.of k)))
    (i : P ⟶ G),
    IsPseudoParabolicSubgroup i →
      ∀ (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q),
        IsSeparated Q.hom → LocallyOfFiniteType Q.hom → QuasiCompact Q.hom →
        Smooth q.left → Surjective q.left → QuasiCompact q.left →
        (∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
          g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) →
        IsPseudoComplete Q

end Langlands.GroupScheme
