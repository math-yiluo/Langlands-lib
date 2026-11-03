import Langlands.GroupScheme.Absolute.Borel
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Scheme quotients by smooth closed subgroups -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A smooth closed subgroup of a smooth affine group over a field has an actual
separated finite-type scheme quotient, with a smooth surjective quasi-compact
projection and exact right-coset fibers on every scheme test. -/
def SmoothSubgroupQuotientExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G),
    IsClosedSubgroup i → Smooth H.X.hom →
      ∃ (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q),
        IsSeparated Q.hom ∧ LocallyOfFiniteType Q.hom ∧ QuasiCompact Q.hom ∧
        Smooth q.left ∧ Surjective q.left ∧ QuasiCompact q.left ∧
        ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
          g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T

/-- Any actual homogeneous quotient by an existing parabolic subgroup of a
connected smooth affine group is proper over the field. -/
def ParabolicSubgroupQuotientProperStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom],
    ConnectedSpace G.X.left →
    ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G),
      IsParabolicSubgroup i →
      ∀ (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q),
        IsSeparated Q.hom → LocallyOfFiniteType Q.hom → QuasiCompact Q.hom →
        Smooth q.left → Surjective q.left → QuasiCompact q.left →
        (∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
          g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) →
        IsProper Q.hom

end Langlands.GroupScheme
