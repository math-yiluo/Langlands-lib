import Langlands.GroupScheme.PseudoParabolic
import Langlands.GroupScheme.HomogeneousQuotientStatement
import Langlands.AlgebraicGeometry.PointTopology.SchemePoints

/-! # Zariski local sections of pseudo-parabolic quotients

This proposition states the local-sections conclusion of CGP Lemma C.2.1 over
infinite fields, at every topological point of a supplied quotient model.
-/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over every infinite field, an actual pseudo-parabolic quotient has algebraic
sections on Zariski neighborhoods of all its topological points. -/
def PseudoParabolicQuotientLocalSectionsStatement : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom],
    ConnectedSpace G.X.left →
    ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G),
      IsPseudoParabolicSubgroup i →
      ∀ (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q),
        IsSeparated Q.hom → LocallyOfFiniteType Q.hom → QuasiCompact Q.hom →
        Smooth q.left → Surjective q.left → QuasiCompact q.left →
        (∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
          g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) →
        ∀ x : Q.left, ∃ (U : Q.left.Opens) (s : openOver k Q U ⟶ G.X),
          x ∈ U ∧ s ≫ q = openOverι k Q U

end Langlands.GroupScheme
