import Langlands.GroupScheme.Rational.WeightSemigroup

/-! # Exact cross-exclusion and the weight spans of ordered-product factors -/

noncomputable section

universe u v w

namespace Langlands.GroupScheme.RelativeRoot

namespace WeightPartition

variable {M : Type v} [Add M] {ι : Type w}
    {Ψ : ι → Set M} {Ω : Set M}

/-- Exact cross-exclusion already implies disjointness of the original blocks. -/
theorem disjoint_of_cross_exclusion
    (hcross : ∀ r q : ι, r ≠ q →
      Disjoint (Ψ r) (AddSubsemigroup.closure (Ψ q) : Set M))
    {r q : ι} (hrq : r ≠ q) : Disjoint (Ψ r) (Ψ q) :=
  (hcross r q hrq).mono_right AddSubsemigroup.subset_closure

/-- A generated block contains no occurring weight outside its own block.
The generated semigroups may still overlap outside the total support. -/
theorem closure_inter_support
    (hcover : (⋃ r, Ψ r) = Ω)
    (hcross : ∀ r q : ι, r ≠ q →
      Disjoint (Ψ r) (AddSubsemigroup.closure (Ψ q) : Set M))
    (r : ι) : (AddSubsemigroup.closure (Ψ r) : Set M) ∩ Ω = Ψ r := by
  classical
  apply Set.Subset.antisymm
  · rintro χ ⟨hχ, hΩ⟩
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp (hcover.symm ▸ hΩ)
    by_cases hqr : q = r
    · simpa [hqr] using hq
    · exact (Set.disjoint_left.mp (hcross q r hqr) hq hχ).elim
  · intro χ hχ
    exact ⟨AddSubsemigroup.subset_closure hχ, hcover ▸ Set.mem_iUnion.mpr ⟨r, hχ⟩⟩

omit [Add M] in
/-- Restricting every block to a subset of the support still covers that subset,
including when the index type is empty. -/
theorem restricted_cover
    (hcover : (⋃ r, Ψ r) = Ω) {Ω' : Set M} (hsub : Ω' ⊆ Ω) :
    (⋃ r, Ψ r ∩ Ω') = Ω' := by
  apply Set.Subset.antisymm
  · intro χ hχ
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hχ
    exact hr.2
  · intro χ hχ
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp (hcover.symm ▸ hsub hχ)
    exact Set.mem_iUnion.mpr ⟨r, hr, hχ⟩

/-- The precise cross-exclusion hypothesis passes to arbitrary restrictions
of the blocks, by monotonicity of positive semigroup generation. -/
theorem restricted_cross_exclusion
    (hcross : ∀ r q : ι, r ≠ q →
      Disjoint (Ψ r) (AddSubsemigroup.closure (Ψ q) : Set M))
    (Ω' : Set M) (r q : ι) (hrq : r ≠ q) :
    Disjoint (Ψ r ∩ Ω')
      (AddSubsemigroup.closure (Ψ q ∩ Ω') : Set M) :=
  (hcross r q hrq).mono Set.inter_subset_left
    (AddSubsemigroup.closure_mono Set.inter_subset_left)

section Zero

variable [Zero M]

/-- If zero occurs, it lies in exactly one original block and no other generated
semigroup contains it. This uses cross-exclusion rather than disjoint closures. -/
theorem exists_unique_zero_block
    (hcover : (⋃ r, Ψ r) = Ω)
    (hcross : ∀ r q : ι, r ≠ q →
      Disjoint (Ψ r) (AddSubsemigroup.closure (Ψ q) : Set M))
    (hzero : (0 : M) ∈ Ω) :
    ∃ r : ι, 0 ∈ Ψ r ∧
      (∀ q : ι, 0 ∈ Ψ q → q = r) ∧
      (∀ q : ι, q ≠ r → 0 ∉ AddSubsemigroup.closure (Ψ q)) := by
  classical
  obtain ⟨r, hr⟩ := Set.mem_iUnion.mp (hcover.symm ▸ hzero)
  refine ⟨r, hr, ?_, ?_⟩
  · intro q hq
    by_contra hqr
    exact Set.disjoint_left.mp (hcross q r hqr) hq (AddSubsemigroup.subset_closure hr)
  · intro q hqr hq
    exact Set.disjoint_left.mp (hcross r q hqr.symm) hr hq

end Zero

end WeightPartition

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

section ActualWeightSpans

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The intrinsic Lie subspace spanned by the actual weight spaces with characters
in a specified set. No semigroup closure or zero character is inserted. -/
def actionWeightSpan (b : AutomorphicAction S.toGrp G)
    (Ξ : Set (characterLattice S)) : Submodule k (Additive (lieKernel G k)) :=
  ⨆ χ : Ξ, actionWeightSpace b χ.val

/-- A character outside the actual total support has zero weight space. -/
theorem actionWeightSpace_eq_bot_of_not_mem_support
    (b : AutomorphicAction S.toGrp G) {χ : characterLattice S}
    (hχ : χ ∉ actionWeightSupport b ⊤) : actionWeightSpace b χ = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro X hX
  by_contra hn
  exact hχ ⟨X, hn, hX, Subgroup.mem_top _⟩

/-- Discarding characters outside the actual total support does not change
the intrinsic weight span. -/
theorem actionWeightSpan_inter_support (b : AutomorphicAction S.toGrp G)
    (Ξ : Set (characterLattice S)) :
    actionWeightSpan b (Ξ ∩ actionWeightSupport b ⊤) = actionWeightSpan b Ξ := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro χ
    exact le_iSup_of_le ⟨χ.val, χ.property.1⟩ le_rfl
  · apply iSup_le
    intro χ
    by_cases hχ : χ.val ∈ actionWeightSupport b ⊤
    · exact le_iSup_of_le ⟨χ.val, χ.property, hχ⟩ le_rfl
    · rw [actionWeightSpace_eq_bot_of_not_mem_support b hχ]
      exact bot_le

/-- Under exactly CGP's cross-exclusion hypothesis, the canonical semigroup
weight span for a factor is the span of its original block. -/
theorem semigroupWeightSpan_closure_eq
    (b : AutomorphicAction S.toGrp G) {I : Type v}
    (Ψ : I → Set (characterLattice S))
    (hcover : (⋃ r, Ψ r) = actionWeightSupport b ⊤)
    (hcross : ∀ r q : I, r ≠ q →
      Disjoint (Ψ r)
        (AddSubsemigroup.closure (Ψ q) : Set (characterLattice S)))
    (r : I) :
    semigroupWeightSpan b (AddSubsemigroup.closure (Ψ r)) =
      actionWeightSpan b (Ψ r) := by
  change actionWeightSpan b (AddSubsemigroup.closure (Ψ r) : Set _) = _
  rw [← actionWeightSpan_inter_support b,
    WeightPartition.closure_inter_support hcover hcross r]

end ActualWeightSpans

end Langlands.GroupScheme.RelativeRoot
