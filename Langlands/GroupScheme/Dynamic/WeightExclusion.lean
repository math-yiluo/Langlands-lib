import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.Absolute.RegularCocharacterWeights

/-! # Weight signs in the actual Lie image of a dynamic parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Dynamic parabolic membership of an actual Lie point is membership in the
nonnegative character-weight span. -/
theorem mem_nonnegativeWeightSpan_iff_mem_parabolic
    (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) (X : Additive (lieKernel G k)) :
    X ∈ nonnegativeWeightSpan j ν ↔
      X.toMul.val ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)).carrier _ := by
  rw [← iSup_nat_weightSpace_cocharacter_eq_nonnegativeWeightSpan hT ν j]
  exact ((dynamicLie k G (CommGroupScheme.groupHom ν ≫ j) X.toMul).2.1).symm

/-- A nonzero character-weight vector in a dynamic parabolic has nonnegative
pairing with its defining cocharacter. -/
theorem latticePairing_nonneg_of_weight_mem_parabolic
    (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) {α : characterLattice T}
    {X : Additive (lieKernel G k)} (hX : X ∈ weightSpace j α) (hne : X ≠ 0)
    (hP : X.toMul.val ∈
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)).carrier _) :
    0 ≤ latticePairing T α ν := by
  by_contra hn
  have hspan := (mem_nonnegativeWeightSpan_iff_mem_parabolic hT j ν X).2 hP
  have hd := weightSpace_disjoint_iSup hT j (p := fun χ => 0 ≤ latticePairing T χ ν) hn
  exact hne (Submodule.disjoint_def.mp hd X hX hspan)

/-- Every nonzero weight in the actual Lie image of a subgroup contained in a
dynamic parabolic pairs nonnegatively with its cocharacter. -/
theorem latticePairing_nonneg_of_lieImage_range_le_parabolic
    (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ G)
    (ν : cocharacterLattice T)
    {H : GroupScheme (Spec (CommRingCat.of k))} (i : H ⟶ G)
    (hP : SubgroupFunctor.range i ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j))
    {α : characterLattice T}
    (h : ∃ X ∈ weightSpace j α, X ≠ 0 ∧
      ∃ Y : lieKernel H k, Y.val ≫ i.hom.hom = X.toMul.val) :
    0 ≤ latticePairing T α ν := by
  obtain ⟨X, hX, hne, Y, hY⟩ := h
  exact latticePairing_nonneg_of_weight_mem_parabolic hT j ν hX hne
    (hP _ (SubgroupFunctor.mem_range.2 ⟨Y.val, hY⟩))

/-- Containment in a dynamic parabolic excludes two opposite nonzero Lie-image
weights whenever their pairing with its cocharacter is nonzero. -/
theorem not_meets_oppositeWeightSpaces_of_range_le_parabolic
    (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ G)
    (ν : cocharacterLattice T)
    {H : GroupScheme (Spec (CommRingCat.of k))} (i : H ⟶ G)
    (hP : SubgroupFunctor.range i ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j))
    (α : characterLattice T) (hα : latticePairing T α ν ≠ 0) :
    ¬ ((∃ X ∈ weightSpace j α, X ≠ 0 ∧
        ∃ Y : lieKernel H k, Y.val ≫ i.hom.hom = X.toMul.val) ∧
      (∃ X ∈ weightSpace j (-α), X ≠ 0 ∧
        ∃ Y : lieKernel H k, Y.val ≫ i.hom.hom = X.toMul.val)) := by
  rintro ⟨hpos, hneg⟩
  have hp := latticePairing_nonneg_of_lieImage_range_le_parabolic hT j ν i hP hpos
  have hn := latticePairing_nonneg_of_lieImage_range_le_parabolic hT j ν i hP hneg
  rw [map_neg, LinearMap.neg_apply] at hn
  exact hα (le_antisymm (neg_nonneg.mp hn) hp)

end Langlands.GroupScheme
