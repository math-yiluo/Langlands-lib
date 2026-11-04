import Langlands.GroupScheme.Reductive.Basic
import Mathlib.FieldTheory.Perfect

/-! # Pseudo-reductivity and reductivity over a perfect field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over a perfect field, triviality of the ground-field unipotent radical
of a smooth connected affine group is equivalent to triviality of its
geometric unipotent radical. -/
def PerfectFieldPseudoReductiveStatement : Prop :=
  ∀ (k : Type u) [Field k] [PerfectField k]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsPseudoReductive G ↔ IsConnectedReductive G

end Langlands.GroupScheme
