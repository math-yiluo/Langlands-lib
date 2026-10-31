import Langlands.Representation.Classification.UniformRefinementCombinatorics
import Langlands.Representation.Classification.TwoSourceShuffleLabels

/-! Exact finite indices for divisible uniform source refinements. -/

noncomputable section

namespace Langlands.Classification.ShuffleRefinement

open GeneralLinear Geometric CuspidalSupport

section General

variable {K : Type*} [Field K] {n : ℕ}
variable (B C : BlockShape n) (w : Equiv.Perm (Fin n)) (S : BlockRefinement B)
variable (hS : sourceLevi K B C w = refinedLevi K B S)

/-- If target blocks remain whole, every source piece fills the target block
containing its image. Minimality and divisibility are unnecessary. -/
theorem sourceBlockEmbedding_surjective_of_contained
    (hc : TargetBlocksContained B C w) (j : Fin B.length) (i : Fin (S j).length) :
    Function.Surjective (sourceBlockEmbedding B C w S hS j i) := by
  rintro ⟨x, hx⟩
  have hj : blockIndex B (w.symm x) = j := by
    have hh := hc x (w (B.index j ((S j).index i ⟨0, (S j).positive i⟩))) hx
    simpa only [Equiv.symm_apply_apply, blockIndex_index] using hh
  obtain ⟨a, ha⟩ := exists_index_of_blockIndex_eq B hj
  have hwa : w (B.index j a) = x :=
    (congrArg w ha).trans (w.apply_symm_apply x)
  have hi : blockIndex (S j) a = i := by
    have hh := (SegmentEdge.sameBlock_of_sourceLevi_eq B C w S hS j a
      ((S j).index i ⟨0, (S j).positive i⟩)).mpr (by
        simpa only [hwa] using hx)
    exact hh.trans (blockIndex_index (S j) i _)
  obtain ⟨b, hb⟩ := exists_index_of_blockIndex_eq (S j) hi
  refine ⟨b, Subtype.ext ?_⟩
  change w (B.index j ((S j).index i b)) = x
  rw [hb, hwa]

include hS in
/-- Whole target blocks identify each source piece's size with its target size. -/
theorem source_size_eq_target_of_contained
    (hc : TargetBlocksContained B C w) (j : Fin B.length) (i : Fin (S j).length) :
    (S j).size i =
      C.size (blockIndex C (w (B.index j ((S j).index i ⟨0, (S j).positive i⟩)))) := by
  have hh := Nat.card_congr (Equiv.ofBijective
    (sourceBlockEmbedding B C w S hS j i)
    ⟨(sourceBlockEmbedding B C w S hS j i).injective,
      sourceBlockEmbedding_surjective_of_contained B C w S hS hc j i⟩)
  simpa only [Nat.card_fin, TotalConjugatingCount.card_blockIndex_fiber] using hh

end General

section Uniform

variable {K : Type*} [Field K]
variable {m r : ℕ} (hr : 0 < r)
variable (B : BlockShape (m * r)) (w : Equiv.Perm (Fin (m * r)))
variable (S : BlockRefinement B)
variable (hS : sourceLevi K B (BlockShape.uniform m r hr) w = refinedLevi K B S)

include hS in
theorem source_size_eq_of_contained
    (hc : TargetBlocksContained B (BlockShape.uniform m r hr) w)
    (j : Fin B.length) (i : Fin (S j).length) :
    (S j).size i = r :=
  source_size_eq_target_of_contained B (BlockShape.uniform m r hr) w S hS hc j i

include hS in
/-- Divisibility of every source-refinement piece is exactly whole-target
containment. This equivalence does not require a minimal permutation. -/
theorem source_divisible_iff_contained :
    (∀ j i, r ∣ (S j).size i) ↔
      TargetBlocksContained B (BlockShape.uniform m r hr) w := by
  refine ⟨inverse_same_source_block hr B w S hS, ?_⟩
  intro hc j i
  rw [source_size_eq_of_contained hr B w S hS hc j i]

end Uniform

section Families

variable {K : Type*} [Field K]
variable {m r : ℕ} (hr : 0 < r) (B : BlockShape (m * r))
variable (S : MinimalRepresentatives B (BlockShape.uniform m r hr) → BlockRefinement B)
variable (hS : ∀ w, sourceLevi K B (BlockShape.uniform m r hr) w.val =
  refinedLevi K B (S w))

/-- Minimal permutations whose specified source refinements have divisible
piece sizes. The refinements themselves are supplied, not chosen here. -/
abbrev DivisibleRefinementRepresentatives : Type :=
  {w : MinimalRepresentatives B (BlockShape.uniform m r hr) //
    ∀ j i, r ∣ (S w j).size i}

/-- A refinement family changes only the predicate: the equivalence preserves
the underlying actual minimal permutation. -/
def divisibleEquivWholeTarget :
    DivisibleRefinementRepresentatives hr B S ≃ WholeTargetRepresentatives hr B :=
  Equiv.subtypeEquivRight (fun w =>
    source_divisible_iff_contained hr B w.val (S w) (hS w))

@[simp] theorem divisibleEquivWholeTarget_val (w : DivisibleRefinementRepresentatives hr B S) :
    (divisibleEquivWholeTarget hr B S hS w).val = w.val := rfl

/-- Thus the finite indices are independent of which standard source refinement
family realizes the actual intersections. -/
def divisibleRefinementEquiv
    (S' : MinimalRepresentatives B (BlockShape.uniform m r hr) → BlockRefinement B)
    (hS' : ∀ w, sourceLevi K B (BlockShape.uniform m r hr) w.val =
      refinedLevi K B (S' w)) :
    DivisibleRefinementRepresentatives hr B S ≃
      DivisibleRefinementRepresentatives hr B S' :=
  (divisibleEquivWholeTarget hr B S hS).trans
    (divisibleEquivWholeTarget hr B S' hS').symm

end Families

section TwoSource

variable {K : Type*} [Field K]
variable {m₀ m₁ r : ℕ} (hr : 0 < r)
variable (B : BlockShape ((m₀ + m₁) * r)) (h₂ : B.length = 2)
variable (h₀ : B.size (Fin.cast h₂.symm 0) = m₀ * r)
variable (h₁ : B.size (Fin.cast h₂.symm 1) = m₁ * r)
variable
  (S : MinimalRepresentatives B (BlockShape.uniform (m₀ + m₁) r hr) → BlockRefinement B)
variable (hS : ∀ w, sourceLevi K B (BlockShape.uniform (m₀ + m₁) r hr) w.val =
  refinedLevi K B (S w))

/-- Exactly the divisible-refinement indices are parametrized by shuffle subsets. -/
def divisibleEquivShuffles :
    DivisibleRefinementRepresentatives hr B S ≃
      {A : Finset (Fin (m₀ + m₁)) // A.card = m₀} :=
  (divisibleEquivWholeTarget hr B S hS).trans
    (wholeTargetEquivShuffles hr B h₂ h₀ h₁)

/-- The forward map uses the same target-block labels as the realized shuffle. -/
theorem divisibleEquivShuffles_val (w : DivisibleRefinementRepresentatives hr B S) :
    (divisibleEquivShuffles hr B h₂ h₀ h₁ S hS w).val =
      binarySubset (fun t => Fin.cast h₂ (targetBlockLabel B
        (BlockShape.uniform (m₀ + m₁) r hr) w.val.val t)) := rfl

/-- The inverse is the actual increasing-coordinate permutation attached to
the subset's binary labeling. -/
theorem divisibleEquivShuffles_symm_val
    (A : {A : Finset (Fin (m₀ + m₁)) // A.card = m₀}) :
    ((divisibleEquivShuffles hr B h₂ h₀ h₁ S hS).symm A).val.val =
      permutationFromLabels hr B (assignmentFromSubset B h₂ h₀ h₁ A) := rfl

include h₂ h₀ h₁ hS in
theorem card_divisibleRefinementRepresentatives :
    Nat.card (DivisibleRefinementRepresentatives hr B S) =
      (m₀ + m₁).choose m₀ := by
  rw [Nat.card_congr (divisibleEquivShuffles hr B h₂ h₀ h₁ S hS),
    Nat.card_eq_fintype_card, Fintype.card_finset_len, Fintype.card_fin]

end TwoSource

end Langlands.Classification.ShuffleRefinement
