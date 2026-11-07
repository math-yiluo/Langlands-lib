import Langlands.GroupScheme.Rational.NestedParabolicLeviCone

/-! # A proper simple-root index from a nonstrict nonnegative exponent -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ParabolicRootPresentation

open RealTorusSpace

variable {k : Type u} [Field k]
  {G P M : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {B : CommGroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {m : M ⟶ P} {b : B.toGrp ⟶ M}
  (fine : ParabolicRootPresentation p m b)

/-- The actual complementary simple roots, without identifying roots that
have equal restrictions to the original split component. -/
def complementarySimpleRootFinset : Finset (characterLattice fine.data.T) :=
  (fine.finite_simpleRoots.sdiff (t := fine.data.J)).toFinset

@[simp]
theorem mem_complementarySimpleRootFinset {α : characterLattice fine.data.T} :
    α ∈ fine.complementarySimpleRootFinset ↔
      α ∈ simpleRelativeRoots fine.data.i fine.data.ν ∧ α ∉ fine.data.J :=
  Set.Finite.mem_toFinset _

/-- A choice of nonnegative coefficients on the original complementary
simple roots for a vector in the supplied nonnegative cone. -/
def nonnegRootCoefficients {x : Vstar B} (hx : x ∈ fine.nonnegCone) :
    characterLattice fine.data.T → ℝ :=
  ((mem_restrictedRootNonnegCone_iff_roots fine.data.i fine.data.ν fine.data.J
    fine.data.f fine.finite_simpleRoots fine.complementarySimpleRootFinset
    (fine.finite_simpleRoots.sdiff (t := fine.data.J)).coe_toFinset).mp hx).choose

theorem nonnegRootCoefficients_nonneg {x : Vstar B} (hx : x ∈ fine.nonnegCone)
    {α : characterLattice fine.data.T} (hα : α ∈ fine.complementarySimpleRootFinset) :
    0 ≤ fine.nonnegRootCoefficients hx α :=
  ((mem_restrictedRootNonnegCone_iff_roots fine.data.i fine.data.ν fine.data.J
    fine.data.f fine.finite_simpleRoots fine.complementarySimpleRootFinset
    (fine.finite_simpleRoots.sdiff (t := fine.data.J)).coe_toFinset).mp hx).choose_spec.1 α hα

theorem sum_nonnegRootCoefficients {x : Vstar B} (hx : x ∈ fine.nonnegCone) :
    ∑ α ∈ fine.complementarySimpleRootFinset,
      fine.nonnegRootCoefficients hx α • restrictedRootVector fine.data.f α = x :=
  ((mem_restrictedRootNonnegCone_iff_roots fine.data.i fine.data.ν fine.data.J
    fine.data.f fine.finite_simpleRoots fine.complementarySimpleRootFinset
    (fine.finite_simpleRoots.sdiff (t := fine.data.J)).coe_toFinset).mp hx).choose_spec.2

/-- The old Levi index enlarged by the positive support of the chosen
nonnegative expansion. This is an index, not an asserted parabolic. -/
def boundaryRootIndex {x : Vstar B} (hx : x ∈ fine.nonnegCone) :
    Set (characterLattice fine.data.T) :=
  fine.data.J ∪ {α | α ∈ simpleRelativeRoots fine.data.i fine.data.ν ∧
    0 < fine.nonnegRootCoefficients hx α}

theorem selectedRoots_subset_boundaryRootIndex {x : Vstar B}
    (hx : x ∈ fine.nonnegCone) :
    fine.data.J ⊆ fine.boundaryRootIndex hx :=
  Set.subset_union_left

theorem boundaryRootIndex_subset_simpleRoots {x : Vstar B}
    (hx : x ∈ fine.nonnegCone) :
    fine.boundaryRootIndex hx ⊆ simpleRelativeRoots fine.data.i fine.data.ν := by
  rintro α (hα | hα)
  · exact fine.isCompatible.subset_simpleRoots hα
  · exact hα.1

/-- Missing strict-cone membership forces a missing simple root in the
constructed index, without an independence assumption on restricted roots. -/
theorem boundaryRootIndex_ne_simpleRoots {x : Vstar B}
    (hx : x ∈ fine.nonnegCone) (hstrict : x ∉ fine.positiveCone) :
    fine.boundaryRootIndex hx ≠ simpleRelativeRoots fine.data.i fine.data.ν := by
  intro heq
  apply hstrict
  apply (mem_restrictedRootPositiveCone_iff_roots fine.data.i fine.data.ν fine.data.J
    fine.data.f fine.finite_simpleRoots fine.complementarySimpleRootFinset
    (fine.finite_simpleRoots.sdiff (t := fine.data.J)).coe_toFinset).mpr
  refine ⟨fine.nonnegRootCoefficients hx, ?_, fine.sum_nonnegRootCoefficients hx⟩
  intro α hα
  have hα' := fine.mem_complementarySimpleRootFinset.mp hα
  have hmem : α ∈ fine.boundaryRootIndex hx := heq.symm ▸ hα'.1
  exact (hmem.resolve_left hα'.2).2

/-- A nonstrict nonnegative vector has an original complementary simple root
with coefficient zero, omitted by the constructed index. -/
theorem exists_zero_coefficient_outside_boundaryRootIndex {x : Vstar B}
    (hx : x ∈ fine.nonnegCone) (hstrict : x ∉ fine.positiveCone) :
    ∃ α ∈ fine.complementarySimpleRootFinset,
      fine.nonnegRootCoefficients hx α = 0 ∧ α ∉ fine.boundaryRootIndex hx := by
  classical
  obtain ⟨α, hα, hnot⟩ :=
    Set.not_subset.mp (show ¬ simpleRelativeRoots fine.data.i fine.data.ν ⊆
      fine.boundaryRootIndex hx from fun h =>
        fine.boundaryRootIndex_ne_simpleRoots hx hstrict
          (Set.Subset.antisymm (fine.boundaryRootIndex_subset_simpleRoots hx) h))
  have hαJ : α ∉ fine.data.J :=
    fun h => hnot (fine.selectedRoots_subset_boundaryRootIndex hx h)
  have hmem := fine.mem_complementarySimpleRootFinset.mpr ⟨hα, hαJ⟩
  refine ⟨α, hmem, le_antisymm ?_ (fine.nonnegRootCoefficients_nonneg hx hmem), hnot⟩
  exact not_lt.mp (fun h => hnot (Or.inr ⟨hα, h⟩))

/-- Restriction along a genuine split-torus map kills the vector when it
kills the selected roots and every root in its positive coefficient support. -/
theorem restrict_eq_zero_of_boundaryRootIndex
    {A : CommGroupScheme (Spec (CommRingCat.of k))}
    (e : A ⟶ B) {x : Vstar B} (hx : x ∈ fine.nonnegCone)
    (hzero : ∀ α ∈ fine.boundaryRootIndex hx, e ≫ fine.data.f ≫ α = 0) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom e) x = 0 := by
  classical
  rw [← fine.sum_nonnegRootCoefficients hx, map_sum]
  apply Finset.sum_eq_zero
  intro α hα
  rw [map_smul]
  by_cases hc : fine.nonnegRootCoefficients hx α = 0
  · rw [hc, zero_smul]
  · have hpos : 0 < fine.nonnegRootCoefficients hx α :=
      lt_of_le_of_ne (fine.nonnegRootCoefficients_nonneg hx hα) (Ne.symm hc)
    have hmem : α ∈ fine.boundaryRootIndex hx :=
      Or.inr ⟨(fine.mem_complementarySimpleRootFinset.mp hα).1, hpos⟩
    rw [restrictedRootVector_eq_tmul, rationalCharacterRestrictReal_tmul]
    change fine.nonnegRootCoefficients hx α •
      ((1 : ℝ) ⊗ₜ[ℤ] (e ≫ fine.data.f ≫ α)) = 0
    rw [hzero α hmem, tmul_zero, smul_zero]

section Nested

variable {Q L : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom L.X.hom] [LocallyOfFiniteType L.X.hom]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {q : Q ⟶ G} {l : L ⟶ Q} {a : A.toGrp ⟶ L}
  (outer : ParabolicRootPresentation q l a)
  (i : M ⟶ L) (hi : i ≫ l ≫ q = m ≫ p)
  (hG : IsConnectedReductive G)
  (hP : SubgroupFunctor.range p ≤ SubgroupFunctor.range q)

include hG hP in
/-- If the constructed support lies in the actual larger Levi's simple-root
face, the original vector restricts to zero on its split component. -/
theorem outerComponentRestriction_eq_zero_of_boundaryRootIndex
    {x : Vstar B} (hx : x ∈ fine.nonnegCone)
    (hface : fine.boundaryRootIndex hx ⊆ fine.outerSimpleRootFace outer i hi) :
    fine.outerComponentRestriction outer i hi x = 0 := by
  classical
  rw [← fine.sum_nonnegRootCoefficients hx, map_sum]
  apply Finset.sum_eq_zero
  intro α hα
  rw [map_smul]
  by_cases hc : fine.nonnegRootCoefficients hx α = 0
  · rw [hc, zero_smul]
  · have hpos : 0 < fine.nonnegRootCoefficients hx α :=
      lt_of_le_of_ne (fine.nonnegRootCoefficients_nonneg hx hα) (Ne.symm hc)
    have hmem : α ∈ fine.boundaryRootIndex hx :=
      Or.inr ⟨(fine.mem_complementarySimpleRootFinset.mp hα).1, hpos⟩
    have hroot : α ∈ relativeRoots (fine.outerFineTorusFactor outer i hi) := by
      have hsimple : α ∈
          simpleRelativeRoots (fine.outerFineTorusFactor outer i hi) fine.data.ν := by
        rw [fine.simpleRelativeRoots_outerFineTorusFactor outer i hi hG hP]
        exact hface hmem
      exact hsimple.1.1
    rw [fine.outerComponentRestriction_restrictedRootVector outer i hi,
      restrictedRootVector_eq_tmul, fine.outerRoot_restrict_eq_zero outer i hi hroot,
      tmul_zero, smul_zero]

end Nested

end Langlands.GroupScheme.ParabolicRootPresentation
