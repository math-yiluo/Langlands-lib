import Langlands.GroupScheme.Rational.RelativeWeylFaithfulness
import Langlands.GroupScheme.Rational.RelativeWeylRootPermutation

/-! # Relative Weyl faithfulness and finiteness from joint spanning -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

/-- Equality of the permutation and root-span kernels, at an individual class. -/
theorem IsSplitTorus.relativeWeylRootPermutation_eq_one_iff
    (hT : IsSplitTorus T.toGrp) (w : relativeWeylGroup i) :
    relativeWeylRootPermutation i w = 1 ↔ relativeWeylAction i w = 1 := by
  change w ∈ (relativeWeylRootPermutation i).ker ↔
    w ∈ (relativeWeylAction i).ker
  rw [hT.relativeWeylRootPermutation_ker i]

/-- Joint spanning by actual roots and restricted group characters implies
faithfulness of the permutation action. Spanning remains an explicit premise. -/
theorem IsSplitTorus.relativeWeylRootPermutation_injective_of_span
    (hT : IsSplitTorus T.toGrp)
    (hspan : Submodule.span ℚ
      (toRat '' (relativeRoots i ∪ Set.range (torusCharacterRestrict i))) = ⊤) :
    Function.Injective (relativeWeylRootPermutation i) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  apply hT.relativeWeylAction_injective_of_span i hspan
  rw [map_one]
  exact (hT.relativeWeylRootPermutation_eq_one_iff i w).mp hw

variable [LocallyOfFiniteType G.X.hom]

/-- Finiteness of the actual relative Weyl quotient from joint spanning and
finite root support, without a root-system premise. -/
theorem IsSplitTorus.finite_relativeWeylGroup_of_span
    (hT : IsSplitTorus T.toGrp)
    (hspan : Submodule.span ℚ
      (toRat '' (relativeRoots i ∪ Set.range (torusCharacterRestrict i))) = ⊤) :
    Finite (relativeWeylGroup i) :=
  hT.finite_relativeWeylGroup_of_action_injective i
    (hT.relativeWeylAction_injective_of_span i hspan)

/-- A finite enumeration of the actual quotient under the joint-span premise. -/
@[instance_reducible]
def relativeWeylGroupFintypeOfSpan
    (hT : IsSplitTorus T.toGrp)
    (hspan : Submodule.span ℚ
      (toRat '' (relativeRoots i ∪ Set.range (torusCharacterRestrict i))) = ⊤) :
    Fintype (relativeWeylGroup i) :=
  letI := hT.finite_relativeWeylGroup_of_span i hspan
  Fintype.ofFinite _

end Langlands.GroupScheme
