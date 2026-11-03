import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Represented ground-field unipotent radicals

These predicates characterize representatives by greatest all-test image containment.
They neither choose a radical nor assert that one exists.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
variable {G U V : GroupScheme (Spec (CommRingCat.of k))}

/-- A represented ground-field unipotent radical, greatest among all smooth connected
unipotent normal closed subgroups over the ground field itself. -/
structure IsUnipotentRadical (i : U ⟶ G) : Prop where
  isClosedSubgroup : IsClosedSubgroup i
  smooth : Smooth U.X.hom
  connectedSpace : ConnectedSpace U.X.left
  isUnipotent : IsUnipotent U
  isNormal : (SubgroupFunctor.range i).IsNormal
  greatest : ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
    IsClosedSubgroup j → Smooth H.X.hom → ConnectedSpace H.X.left → IsUnipotent H →
      (SubgroupFunctor.range j).IsNormal → SubgroupFunctor.range j ≤ SubgroupFunctor.range i

/-- A represented split ground-field unipotent radical, greatest among the split
smooth connected unipotent normal closed subgroups. Split unipotence is the existing
finite-series predicate with represented fppf Ga quotients. -/
structure IsSplitUnipotentRadical (i : U ⟶ G) : Prop where
  isClosedSubgroup : IsClosedSubgroup i
  smooth : Smooth U.X.hom
  connectedSpace : ConnectedSpace U.X.left
  isUnipotent : IsUnipotent U
  isSplitUnipotent : RelativeRoot.IsSplitUnipotent U
  isNormal : (SubgroupFunctor.range i).IsNormal
  greatest : ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
    IsClosedSubgroup j → Smooth H.X.hom → ConnectedSpace H.X.left → IsUnipotent H →
      RelativeRoot.IsSplitUnipotent H → (SubgroupFunctor.range j).IsNormal →
        SubgroupFunctor.range j ≤ SubgroupFunctor.range i

namespace IsUnipotentRadical

variable {i : U ⟶ G} {j : V ⟶ G}

/-- Greatest represented radicals have the same image on every test scheme. -/
theorem range_eq (hi : IsUnipotentRadical i) (hj : IsUnipotentRadical j) :
    SubgroupFunctor.range i = SubgroupFunctor.range j :=
  le_antisymm
    (hj.greatest U i hi.isClosedSubgroup hi.smooth hi.connectedSpace hi.isUnipotent hi.isNormal)
    (hi.greatest V j hj.isClosedSubgroup hj.smooth hj.connectedSpace hj.isUnipotent hj.isNormal)

/-- If the ground-field radical is trivial in the existing sense, any representative
has trivial image on all tests. -/
theorem range_eq_bot (hi : IsUnipotentRadical i) (hG : HasTrivialUnipotentRadical G) :
    SubgroupFunctor.range i = ⊥ :=
  hG U i hi.isClosedSubgroup hi.smooth hi.connectedSpace hi.isUnipotent hi.isNormal

/-- Given a represented radical, the existing triviality predicate is exactly
triviality of its all-test image. -/
theorem hasTrivialUnipotentRadical_iff (hi : IsUnipotentRadical i) :
    HasTrivialUnipotentRadical G ↔ SubgroupFunctor.range i = ⊥ := by
  constructor
  · exact hi.range_eq_bot
  · intro hi0 H j hj hs hc hu hn
    have hle := hi.greatest H j hj hs hc hu hn
    rw [hi0] at hle
    apply SubgroupFunctor.ext
    intro T
    exact le_antisymm (hle T) bot_le

/-- A ground-field radical which is split also satisfies the split radical predicate. -/
theorem isSplitUnipotentRadical (hi : IsUnipotentRadical i)
    (hs : RelativeRoot.IsSplitUnipotent U) : IsSplitUnipotentRadical i where
  isClosedSubgroup := hi.isClosedSubgroup
  smooth := hi.smooth
  connectedSpace := hi.connectedSpace
  isUnipotent := hi.isUnipotent
  isSplitUnipotent := hs
  isNormal := hi.isNormal
  greatest H j hj hsm hc hu _ hn := hi.greatest H j hj hsm hc hu hn

end IsUnipotentRadical

namespace IsSplitUnipotentRadical

variable {i : U ⟶ G} {j : V ⟶ G}

/-- Greatest split represented radicals have the same image on every test scheme. -/
theorem range_eq (hi : IsSplitUnipotentRadical i) (hj : IsSplitUnipotentRadical j) :
    SubgroupFunctor.range i = SubgroupFunctor.range j :=
  le_antisymm
    (hj.greatest U i hi.isClosedSubgroup hi.smooth hi.connectedSpace hi.isUnipotent
      hi.isSplitUnipotent hi.isNormal)
    (hi.greatest V j hj.isClosedSubgroup hj.smooth hj.connectedSpace hj.isUnipotent
      hj.isSplitUnipotent hj.isNormal)

/-- A represented split ground-field radical lies in every represented ground-field
radical. The two predicates are not identified. -/
theorem range_le_unipotentRadical (hi : IsSplitUnipotentRadical i)
    (hj : IsUnipotentRadical j) : SubgroupFunctor.range i ≤ SubgroupFunctor.range j :=
  hj.greatest U i hi.isClosedSubgroup hi.smooth hi.connectedSpace hi.isUnipotent hi.isNormal

/-- Triviality of the ground-field radical forces every represented split radical
to have trivial all-test image. -/
theorem range_eq_bot (hi : IsSplitUnipotentRadical i)
    (hG : HasTrivialUnipotentRadical G) : SubgroupFunctor.range i = ⊥ :=
  hG U i hi.isClosedSubgroup hi.smooth hi.connectedSpace hi.isUnipotent hi.isNormal

end IsSplitUnipotentRadical

end Langlands.GroupScheme
