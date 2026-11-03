import Langlands.GroupScheme.HomogeneousQuotientStatement

/-! # Existence of a Borel with proper homogeneous quotients -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over an algebraically closed field, some Borel of every connected smooth
affine group has proper actual homogeneous quotients. -/
def SomeBorelQuotientProperStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom],
    ConnectedSpace G.X.left →
      ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G),
        IsBorelSubgroup i ∧
          ∀ (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q),
            IsSeparated Q.hom → LocallyOfFiniteType Q.hom → QuasiCompact Q.hom →
              Smooth q.left → Surjective q.left → QuasiCompact q.left →
                (∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
                  g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) →
                IsProper Q.hom

end Langlands.GroupScheme
