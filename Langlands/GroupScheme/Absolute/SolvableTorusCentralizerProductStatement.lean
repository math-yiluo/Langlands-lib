import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Torus.Lattice
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # A connected solvable group is a unipotent subgroup times a torus centralizer (Milne 16.41) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Theorem 16.41, product clause: let `G` be a smooth connected affine solvable group
over an algebraically closed field `k` and let `j : T ⟶ G` be a torus in `G`. For every
representing subgroup `c : C ⟶ G` of the centralizer of `T`, there is a closed unipotent subgroup
`u : U ⟶ G` such that the multiplication morphism `U × C ⟶ G` is surjective. -/
def SolvableTorusCentralizerProductStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    IsSolvableGroupScheme G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
      IsClosedSubgroup j → IsTorus T.toGrp →
      ∀ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ G),
        (torusCentralizer j).IsRepresentedBy c →
          ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (u : U ⟶ G),
            IsClosedSubgroup u ∧ IsUnipotent U ∧
              Surjective (subgroupMultiplication u c).left

end Langlands.GroupScheme
