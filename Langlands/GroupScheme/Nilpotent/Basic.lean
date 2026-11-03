import Langlands.GroupScheme.Absolute.Borel
import Mathlib.GroupTheory.Nilpotent

/-! # Geometric nilpotence of smooth group schemes over a field -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- Nilpotence of the abstract group of geometric points. As with
`IsSolvableGroupScheme`, this predicate is intended for smooth group schemes. -/
def IsNilpotentGroupScheme (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  Group.IsNilpotent (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))) ⟶
    ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X)

/-- Geometric nilpotence implies the published geometric solvability predicate. -/
theorem IsNilpotentGroupScheme.isSolvableGroupScheme
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsNilpotentGroupScheme G) :
    IsSolvableGroupScheme G := by
  unfold IsNilpotentGroupScheme at hG
  unfold IsSolvableGroupScheme
  let := hG
  infer_instance

end Langlands.GroupScheme
