import Langlands.GroupScheme.Absolute.Borel

/-! # The flag step and the envelope step of Chevalley's Borel-intersection theorem -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Flag step: a smooth connected unipotent closed subgroup lying in every Borel
through a maximal torus lies in every Borel subgroup. This is the step of the
proof of Milne 2017, Theorem 17.56, given by Theorem 17.65 and the argument
following it, applied to the given subgroup in place of `I_u(T)`. -/
def UnipotentTorusBorelsToAllBorelsStatement : Prop :=
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
      ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
        IsBorelSubgroup b → SubgroupFunctor.range i ≤ SubgroupFunctor.range b

/-- Envelope step: a smooth connected unipotent closed subgroup lying in every
Borel subgroup lies in a smooth connected normal unipotent closed subgroup.
This is the final step of the proof of Milne 2017, Theorem 17.56, through
Remark 17.31 and Theorem 16.33 on the unipotent part of the radical. -/
def UnipotentAllBorelsEnvelopeStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G),
      IsClosedSubgroup i → Smooth U.X.hom → ConnectedSpace U.X.left → IsUnipotent U →
      (∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
        IsBorelSubgroup b → SubgroupFunctor.range i ≤ SubgroupFunctor.range b) →
      ∃ (N : GroupScheme (Spec (CommRingCat.of k))) (n : N ⟶ G),
        IsClosedSubgroup n ∧ Smooth N.X.hom ∧ ConnectedSpace N.X.left ∧ IsUnipotent N ∧
          (SubgroupFunctor.range n).IsNormal ∧ SubgroupFunctor.range i ≤ SubgroupFunctor.range n

end Langlands.GroupScheme
