import Langlands.GroupScheme.Trigonalizable
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Subgroups and quotients of trigonalizable groups (Milne 16.3) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Corollary 16.3: closed subgroups and quotients of a trigonalizable affine
algebraic group over a field are trigonalizable. A quotient is a flat surjective homomorphism
onto an affine algebraic group (Milne, Definition 5.5). -/
def TrigonalizableSubgroupQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom],
    IsTrigonalizable G →
      (∀ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G),
        IsClosedSubgroup i → IsTrigonalizable H) ∧
      (∀ (Q : GroupScheme (Spec (CommRingCat.of k)))
        [LocallyOfFiniteType Q.X.hom] [IsAffineHom Q.X.hom] (q : G ⟶ Q),
        Flat q.hom.hom.left → Surjective q.hom.hom.left → IsTrigonalizable Q)

end Langlands.GroupScheme
