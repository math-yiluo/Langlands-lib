import Langlands.GroupScheme.Dynamic.SplitContractingSubgroup
import Langlands.GroupScheme.Rational.ActionCocharacterWeights
import Langlands.GroupScheme.Rational.SemigroupSolvableIntersection
import Langlands.GroupScheme.Rational.TrivialAction
import Langlands.GroupScheme.Rational.WeightVectorUniqueness

/-! # Split-torus rigidity in the absence of split unipotent subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))

/-- Every smooth connected split-unipotent closed subgroup has trivial image
on every relative test. Normality is deliberately not required. -/
def HasNoNontrivialSplitUnipotentSubgroup : Prop :=
  ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
    IsClosedSubgroup j → Smooth H.X.hom → ConnectedSpace H.X.left →
      IsUnipotent H → RelativeRoot.IsSplitUnipotent H →
        SubgroupFunctor.range j = ⊥

namespace AutomorphicAction

open RelativeRoot

variable {G}
    [IsAffineHom G.X.hom]

/-- A trivial identity-limit functor has zero positive tangent-weight span. -/
theorem positiveWeightSpan_eq_bot_of_unipotent_eq_bot
    [LocallyOfFiniteType G.X.hom]
    (a : AutomorphicAction (Gm (Spec (CommRingCat.of k))).toGrp G)
    (ha : a.unipotent = ⊥) : a.positiveWeightSpan = ⊥ := by
  rw [← a.tangentSubmodule_unipotent dynamicLie, ha, tangentSubmodule_bot]

/-- The actual split contracting representative vanishes when the ambient
group has no nontrivial smooth connected split-unipotent closed subgroup. -/
theorem unipotent_eq_bot_of_no_split_unipotent_subgroup
    [Smooth G.X.hom]
    (a : AutomorphicAction (Gm (Spec (CommRingCat.of k))).toGrp G)
    (hG : HasNoNontrivialSplitUnipotentSubgroup G) : a.unipotent = ⊥ := by
  let D := a.splitContractingSubgroup
  exact D.isRepresentedBy.2.symm.trans
    (hG D.group D.inclusion D.isClosedSubgroup D.smooth D.connectedSpace
      D.isUnipotent D.isSplitUnipotent)

variable [Smooth G.X.hom] [ConnectedSpace G.X.left]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (b : AutomorphicAction S.toGrp G) (hS : IsSplitTorus S.toGrp)

include hS

/-- If all cocharacter-restricted contracting subgroups vanish, the full
all-test fixed subgroup of a split-torus action is the ambient group. -/
theorem fixedSubgroup_eq_top_of_cocharacter_unipotent_eq_bot
    (hU : ∀ ν : cocharacterLattice S,
      (b.restrict (CommGroupScheme.groupHom ν)).unipotent = ⊥) :
    b.fixedSubgroup = ⊤ := by
  have hweight : ∀ χ : characterLattice S, χ ≠ 0 → actionWeightSpace b χ = ⊥ := by
    intro χ hχ
    obtain ⟨D, hD, ν, hν⟩ := hS.exists_pairing_eq_pos hχ
    let a := b.restrict (CommGroupScheme.groupHom ν)
    have hpos : a.positiveWeightSpan = ⊥ :=
      a.positiveWeightSpan_eq_bot_of_unipotent_eq_bot (hU ν)
    have hle : actionWeightSpace b χ ≤ a.positiveWeightSpan := by
      unfold positiveWeightSpan
      refine le_iSup_of_le (D - 1) ?_
      rw [actionWeightSpace_cocharacter_eq_iSup b hS ν]
      exact le_iSup_of_le χ (le_iSup_of_le (by omega) le_rfl)
    exact le_antisymm (by simpa only [hpos] using hle) bot_le
  have hzero : actionWeightSpace b 0 = ⊤ := by
    apply top_unique
    rw [← iSup_actionWeightSpace_eq_top b hS]
    refine iSup_le fun χ => ?_
    by_cases hχ : χ = 0
    · rw [hχ]
    · rw [hweight χ hχ]
      exact bot_le
  obtain ⟨C, j, hj, hc, hs⟩ := b.fixedSubgroup_isSmoothClosed hS
  apply eq_top_of_smooth_closed_of_tangentSubmodule_eq_top j hj hc hs
  rw [b.tangentSubmodule_fixedSubgroup_eq_actionWeightSpace_zero, hzero]

/-- Under the same contracting-subgroup hypothesis the actual action
morphism is the second projection. -/
theorem eq_trivial_of_cocharacter_unipotent_eq_bot
    (hU : ∀ ν : cocharacterLattice S,
      (b.restrict (CommGroupScheme.groupHom ν)).unipotent = ⊥) :
    b = trivial S.toGrp G := by
  apply eq_trivial_of_act_eq
  intro T s g
  have hg : g ∈ b.fixedSubgroup.carrier T := by
    rw [b.fixedSubgroup_eq_top_of_cocharacter_unipotent_eq_bot hS hU]
    trivial
  simpa only [Category.id_comp] using hg T (𝟙 T) s

/-- Every actual split-torus action on a smooth connected affine group
without nontrivial split-unipotent closed subgroups is trivial. -/
theorem eq_trivial_of_no_split_unipotent_subgroup
    (hG : HasNoNontrivialSplitUnipotentSubgroup G) :
    b = trivial S.toGrp G := by
  apply b.eq_trivial_of_cocharacter_unipotent_eq_bot hS
  intro ν
  exact (b.restrict (CommGroupScheme.groupHom ν)).unipotent_eq_bot_of_no_split_unipotent_subgroup hG

end AutomorphicAction

end Langlands.GroupScheme
