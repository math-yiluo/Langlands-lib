import Langlands.GroupScheme.Absolute.RationalSubgroupContainment
import Langlands.GroupScheme.Rational.RootSubgroupLieImage
import Langlands.GroupScheme.Rational.RootSubgroupRepresentability
import Langlands.GroupScheme.Rational.RootSubgroupRationalNontrivial
import Langlands.GroupScheme.Rational.SemigroupWeightSupport
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Actual root points outside higher-multiple root groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)

include hS

/-- The actual root functor cannot lie in a root functor whose positive
cyclic support excludes that root. -/
theorem subgroup_not_le_of_not_mem_cyclicTail
    {a b : characterLattice S} (ha : a ∈ relativeRoots i)
    (hb : b ≠ 0) (hab : a ∉ cyclicTail b 1) :
    ¬ subgroup i a ≤ subgroup i b := by
  intro hle
  have hsupp : a ∈ actionWeightSupport (AutomorphicAction.conjugation i)
      (subgroup i a) := by
    apply (HasLieImage.mem_actionWeightSupport_iff
      (AutomorphicAction.conjugation i) hS (cyclicTail a 1)
      (hasLieImage_subgroup i a hS ha.1) a).mpr
    refine ⟨⟨1, by decide, by decide, one_smul ℕ a⟩, ?_⟩
    simpa only [actionWeightSpace_conjugation] using ha.2
  have hsupp' := actionWeightSupport_mono (AutomorphicAction.conjugation i) hle hsupp
  exact hab ((HasLieImage.mem_actionWeightSupport_iff
    (AutomorphicAction.conjugation i) hS (cyclicTail b 1)
    (hasLieImage_subgroup i b hS hb) a).mp hsupp').1

/-- Algebraically closed rational points witness failure of cyclic root
containment, by reducedness and closed representability of the root groups. -/
theorem exists_rootPoint_not_mem_of_not_mem_cyclicTail [IsAlgClosed k]
    {a b : characterLattice S} (ha : a ∈ relativeRoots i)
    (hb : b ≠ 0) (hab : a ∉ cyclicTail b 1) :
    ∃ x : rationalPoints G,
      x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)) ∧
        x ∉ (subgroup i b).carrier (Over.mk (𝟙 _)) := by
  by_contra hnone
  apply subgroup_not_le_of_not_mem_cyclicTail hS i ha hb hab
  obtain ⟨U, jU, hU, _, hUs, _⟩ :=
    subgroup_has_smooth_closed_representative hS i a ha.1
  obtain ⟨V, jV, hV, hVc, _, _⟩ :=
    subgroup_has_smooth_closed_representative hS i b hb
  let : Smooth U.X.hom := hUs
  let : IsReduced U.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k U.X.left U.X.hom
  rw [← hU.2, ← hV.2]
  apply SubgroupFunctor.range_le_of_algClosed_points hVc
  intro x hx
  have hxa : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)) := by
    simpa only [hU.2] using hx
  have hxb : x ∈ (subgroup i b).carrier (Over.mk (𝟙 _)) := by
    by_contra hxnot
    exact hnone ⟨x, hxa, hxnot⟩
  simpa only [hV.2] using hxb

/-- A nonzero split-torus character is not a positive multiple of a strictly
higher positive multiple of itself. -/
theorem not_mem_cyclicTail_nsmul {a : characterLattice S} (ha : a ≠ 0)
    {n : ℕ} (hn : 2 ≤ n) : a ∉ cyclicTail (n • a) 1 := by
  rintro ⟨m, _, hm, he⟩
  have hprod : m * n = 1 := hS.nsmul_character_injective ha
    (by simpa only [smul_smul, one_smul] using he)
  have hle : n ≤ m * n := by
    calc
      n = 1 * n := (one_mul n).symm
      _ ≤ m * n := Nat.mul_le_mul_right n (show 1 ≤ m from hm)
  omega

/-- Every actual root functor strictly contains its higher positive-multiple
root functors, in the sense that the reverse inclusion fails on all tests. -/
theorem subgroup_not_le_nsmul {a : characterLattice S}
    (ha : a ∈ relativeRoots i) {n : ℕ} (hn : 2 ≤ n) :
    ¬ subgroup i a ≤ subgroup i (n • a) := by
  exact subgroup_not_le_of_not_mem_cyclicTail hS i ha
    (hS.nsmul_ne_zero ha.1 (by omega)) (not_mem_cyclicTail_nsmul hS ha.1 hn)

/-- Over an algebraically closed field, an actual root group has a rational
point outside the root group for each higher positive multiple. -/
theorem exists_rootPoint_not_mem_nsmul [IsAlgClosed k]
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ x : rationalPoints G,
      x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)) ∧
        x ∉ (subgroup i (n • a)).carrier (Over.mk (𝟙 _)) :=
  exists_rootPoint_not_mem_of_not_mem_cyclicTail hS i ha
    (hS.nsmul_ne_zero ha.1 (by omega)) (not_mem_cyclicTail_nsmul hS ha.1 hn)

/-- Choose an actual root point outside the specified higher-multiple root
subgroup. Its exclusion, and hence nonidentity, is part of the construction. -/
def rootPointOutsideMultiple [IsAlgClosed k]
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    {n : ℕ} (hn : 2 ≤ n) :
    {x : rationalPoints G //
      x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)) ∧
        x ∉ (subgroup i (n • a)).carrier (Over.mk (𝟙 _))} :=
  ⟨Classical.choose (exists_rootPoint_not_mem_nsmul hS i ha hn),
    Classical.choose_spec (exists_rootPoint_not_mem_nsmul hS i ha hn)⟩

/-- The chosen point is nonidentity because every root subgroup contains the
identity. -/
theorem rootPointOutsideMultiple_ne_one [IsAlgClosed k]
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    {n : ℕ} (hn : 2 ≤ n) : (rootPointOutsideMultiple hS i ha hn).val ≠ 1 := by
  intro h
  apply (rootPointOutsideMultiple hS i ha hn).property.2
  rw [h]
  exact (subgroup i (n • a)).carrier (Over.mk (𝟙 _)) |>.one_mem

end Langlands.GroupScheme.RelativeRoot
