import Langlands.GroupScheme.Absolute.Borel

/-! # A unipotent-envelope consequence of Chevalley's Borel-intersection theorem -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A smooth connected unipotent closed subgroup lying in every Borel through a
maximal torus lies in a smooth connected normal unipotent closed subgroup.
This is the unipotent-envelope consequence of Milne 2017, Theorem 17.56. -/
def ChevalleyUnipotentEnvelopeStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G),
    IsMaximalTorus t →
    ∀ (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G),
      IsClosedSubgroup i → Smooth U.X.hom → ConnectedSpace U.X.left → IsUnipotent U →
      (∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
        IsBorelSubgroup b → SubgroupFunctor.range t ≤ SubgroupFunctor.range b →
          SubgroupFunctor.range i ≤ SubgroupFunctor.range b) →
      ∃ (N : GroupScheme (Spec (CommRingCat.of k))) (n : N ⟶ G),
        IsClosedSubgroup n ∧ Smooth N.X.hom ∧ ConnectedSpace N.X.left ∧ IsUnipotent N ∧
          (SubgroupFunctor.range n).IsNormal ∧ SubgroupFunctor.range i ≤ SubgroupFunctor.range n

end Langlands.GroupScheme
