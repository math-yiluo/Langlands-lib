import Langlands.GroupScheme.PseudoParabolic
import Langlands.GroupScheme.HomogeneousQuotientStatement

/-! # Rational lifting for pseudo-parabolic quotients

This proposition states the rational-point conclusion of CGP Lemma C.2.1 over
every field, for every supplied homogeneous quotient model.
-/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every rational point of an actual pseudo-parabolic quotient lifts to the
ambient group, over any field, including finite and imperfect fields. -/
def PseudoParabolicQuotientRationalLiftingStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom],
    ConnectedSpace G.X.left →
    ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G),
      IsPseudoParabolicSubgroup i →
      ∀ (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q),
        IsSeparated Q.hom → LocallyOfFiniteType Q.hom → QuasiCompact Q.hom →
        Smooth q.left → Surjective q.left → QuasiCompact q.left →
        (∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
          g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) →
        ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q,
          ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X, g ≫ q = x

end Langlands.GroupScheme
