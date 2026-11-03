import Langlands.GroupScheme.Absolute.Borel

/-! # The unipotent part of a smooth connected solvable group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A smooth connected solvable affine group `H` over an algebraically closed field has a
smooth connected normal unipotent closed subgroup `H_u` containing every unipotent closed
subgroup of `H`. This is the algebraically closed case of Milne 2017, Theorem 16.33(a)–(c),
without the clause that `H / H_u` is a torus. -/
def SolvableUnipotentPartStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
    IsSolvableGroupScheme H →
    ∃ (Hu : GroupScheme (Spec (CommRingCat.of k))) (h : Hu ⟶ H),
      IsClosedSubgroup h ∧ Smooth Hu.X.hom ∧ ConnectedSpace Hu.X.left ∧ IsUnipotent Hu ∧
        (SubgroupFunctor.range h).IsNormal ∧
        ∀ (W : GroupScheme (Spec (CommRingCat.of k))) (w : W ⟶ H),
          IsClosedSubgroup w → IsUnipotent W →
            SubgroupFunctor.range w ≤ SubgroupFunctor.range h

end Langlands.GroupScheme
