import Langlands.GroupScheme.Absolute.Borel
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Proper parabolic subgroups and solvability (Milne 17.17) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Corollary 17.17: a smooth connected affine group `G` over an algebraically closed
field `k` has a parabolic subgroup `i : P ⟶ G` that is not an isomorphism if and only if `G` is
not solvable. -/
def ProperParabolicSolvableStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    (∃ (P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G),
        IsParabolicSubgroup i ∧ ¬ IsIso i) ↔
      ¬ IsSolvableGroupScheme G

end Langlands.GroupScheme
