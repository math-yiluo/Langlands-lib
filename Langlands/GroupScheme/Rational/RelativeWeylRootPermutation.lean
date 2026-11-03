import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.Rational.RelativeWeylRootKernel
import Langlands.GroupScheme.Rational.RelativeWeylCharacterAction

/-! # The actual relative Weyl permutation action on roots -/

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
  [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

private theorem characterAction_mapsTo_roots (w : relativeWeylGroup i) :
    Set.MapsTo (relativeWeylCharacterAction i w) (relativeRoots i) (relativeRoots i) := by
  refine Quotient.inductionOn w ?_
  intro n
  exact weylAction_mapsTo_relativeRoots i n

/-- The existing quotient `N(k)/Z(k)` permutes the actual character-valued roots. -/
def relativeWeylRootPermutation :
    relativeWeylGroup i →* Equiv.Perm (relativeRoots i) where
  toFun w :=
    { toFun := fun α =>
        ⟨relativeWeylCharacterAction i w α, characterAction_mapsTo_roots i w α.property⟩
      invFun := fun α =>
        ⟨relativeWeylCharacterAction i w⁻¹ α, characterAction_mapsTo_roots i w⁻¹ α.property⟩
      left_inv := by
        intro α
        apply Subtype.ext
        change relativeWeylCharacterAction i w⁻¹
          (relativeWeylCharacterAction i w α) = α
        rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      right_inv := by
        intro α
        apply Subtype.ext
        change relativeWeylCharacterAction i w
          (relativeWeylCharacterAction i w⁻¹ α) = α
        rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl }
  map_one' := by
    apply Equiv.ext
    intro α
    apply Subtype.ext
    change relativeWeylCharacterAction i 1 α = α
    rw [map_one]
    rfl
  map_mul' w z := by
    apply Equiv.ext
    intro α
    apply Subtype.ext
    change relativeWeylCharacterAction i (w * z) α =
      relativeWeylCharacterAction i w (relativeWeylCharacterAction i z α)
    rw [map_mul, LinearEquiv.mul_apply]

@[simp]
theorem relativeWeylRootPermutation_apply (w : relativeWeylGroup i)
    (α : relativeRoots i) :
    (relativeWeylRootPermutation i w α : characterLattice T) =
      relativeWeylCharacterAction i w α :=
  rfl

/-- The permutation is trivial precisely when every actual root is fixed. -/
theorem relativeWeylRootPermutation_eq_one_iff (w : relativeWeylGroup i) :
    relativeWeylRootPermutation i w = 1 ↔
      ∀ α ∈ relativeRoots i, relativeWeylCharacterAction i w α = α := by
  constructor
  · intro hw α hα
    exact congrArg Subtype.val (Equiv.congr_fun hw ⟨α, hα⟩)
  · intro hw
    apply Equiv.ext
    intro α
    exact Subtype.ext (hw α α.property)

/-- For split tori the root permutation and rational root-span actions have
the same kernel. This is not a faithfulness assertion. -/
theorem IsSplitTorus.relativeWeylRootPermutation_ker (hT : IsSplitTorus T.toGrp) :
    (relativeWeylRootPermutation i).ker = (relativeWeylAction i).ker := by
  apply Subgroup.ext
  intro w
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  change relativeWeylRootPermutation i (QuotientGroup.mk n) = 1 ↔
    relativeWeylAction i (QuotientGroup.mk n) = 1
  rw [relativeWeylRootPermutation_eq_one_iff,
    hT.relativeWeylAction_mk_eq_one_iff i n]
  rfl

/-- Finite root support makes the image of the actual rational root-span
action finite, without assuming a root-system realization. -/
theorem IsSplitTorus.finite_range_relativeWeylAction
    [LocallyOfFiniteType G.X.hom] (hT : IsSplitTorus T.toGrp) :
    Finite (relativeWeylAction i).range := by
  let := relativeRootFintypeOfIsSplitTorus i hT
  have hquot : Finite (relativeWeylGroup i ⧸ (relativeWeylRootPermutation i).ker) :=
    Finite.of_injective
      (QuotientGroup.quotientKerEquivRange (relativeWeylRootPermutation i))
      (QuotientGroup.quotientKerEquivRange (relativeWeylRootPermutation i)).injective
  rw [hT.relativeWeylRootPermutation_ker i] at hquot
  have := hquot
  exact Finite.of_surjective
    (QuotientGroup.quotientKerEquivRange (relativeWeylAction i))
    (QuotientGroup.quotientKerEquivRange (relativeWeylAction i)).surjective

/-- Faithfulness is the remaining hypothesis needed to infer finiteness of
the acting quotient from the finite-image result. -/
theorem IsSplitTorus.finite_relativeWeylGroup_of_action_injective
    [LocallyOfFiniteType G.X.hom] (hT : IsSplitTorus T.toGrp)
    (hfaithful : Function.Injective (relativeWeylAction i)) :
    Finite (relativeWeylGroup i) := by
  have := hT.finite_range_relativeWeylAction i
  exact Finite.of_injective (relativeWeylAction i).rangeRestrict
    (fun _ _ h => hfaithful (congrArg Subtype.val h))

/-- A finite enumeration of the image, rather than of the possibly
nonfaithful acting quotient. -/
@[instance_reducible]
def relativeWeylActionRangeFintypeOfIsSplitTorus
    [LocallyOfFiniteType G.X.hom] (hT : IsSplitTorus T.toGrp) :
    Fintype (relativeWeylAction i).range :=
  letI := hT.finite_range_relativeWeylAction i
  Fintype.ofFinite _

end Langlands.GroupScheme
