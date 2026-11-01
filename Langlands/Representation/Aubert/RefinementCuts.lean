import Langlands.Representation.Geometric.BlockWeylCutProof
import Langlands.Representation.Geometric.MonotoneBlocksProof
import Langlands.Representation.Classification.ProductLeviMinimalIndex
import Langlands.Representation.Geometric.BlockShapeCutCounts
import Mathlib.Data.Nat.Choose.Sum

/-! Refinements of a fixed consecutive block shape in cut coordinates. -/

noncomputable section

namespace Langlands.Aubert

open GeneralLinear Geometric

variable {n : ℕ}

private theorem shape_eq_of_same_blocks {B C : BlockShape n}
    (h : ∀ a b, blockIndex B a = blockIndex B b ↔ blockIndex C a = blockIndex C b) :
    B = C := by
  apply BlockShape.cuts_injective
  apply Finset.Subset.antisymm
  · apply (blockWeyl_le_iff_cuts_subset B C).mp
    intro w hw a
    exact (h (w a) a).mpr (hw a)
  · apply (blockWeyl_le_iff_cuts_subset C B).mp
    intro w hw a
    exact (h (w a) a).mp (hw a)

/-- Flattening a refinement adds cuts to its coarse shape. -/
theorem cuts_subset_flatten (B : BlockShape n) (S : BlockRefinement B) :
    B.cuts ⊆ (B.flatten S).cuts :=
  (blockWeyl_le_iff_cuts_subset B (B.flatten S)).mp
    (ProductLeviMinimalIndex.blockWeyl_flatten_le B S)

/-- A flattened shape determines the refinement of a fixed coarse shape. -/
theorem flatten_refinement_injective (B : BlockShape n) :
    Function.Injective (B.flatten : BlockRefinement B → BlockShape n) := by
  intro S R h
  funext i
  apply shape_eq_of_same_blocks
  intro x y
  rw [← ProductLeviMinimalIndex.blockIndex_flatten_index_eq_iff B S i,
    ← ProductLeviMinimalIndex.blockIndex_flatten_index_eq_iff B R i, h]

/-- Every shape with all the coarse cuts is the flattening of a refinement. -/
theorem exists_refinement_of_cuts_subset (B C : BlockShape n)
    (hBC : B.cuts ⊆ C.cuts) : ∃ S : BlockRefinement B, B.flatten S = C := by
  classical
  have hex (i : Fin B.length) :
      ∃ S : BlockShape (B.size i), ∀ x y,
        blockIndex S x = blockIndex S y ↔
          blockIndex C (B.index i x) = blockIndex C (B.index i y) := by
    obtain ⟨S, hS⟩ := monotoneBlockShape (B.size i) C.length
      (fun x => blockIndex C (B.index i x))
      ((blockIndex_monotone C).comp (index_strictMono B i).monotone)
    refine ⟨S, fun x y => ?_⟩
    simp only [le_antisymm_iff, hS]
  choose S hS using hex
  refine ⟨S, shape_eq_of_same_blocks ?_⟩
  intro a b
  obtain ⟨⟨i, x⟩, rfl⟩ := B.indexEquiv.surjective a
  obtain ⟨⟨j, y⟩, rfl⟩ := B.indexEquiv.surjective b
  change blockIndex (B.flatten S) (B.index i x) =
    blockIndex (B.flatten S) (B.index j y) ↔
      blockIndex C (B.index i x) = blockIndex C (B.index j y)
  by_cases hij : i = j
  · subst j
    rw [ProductLeviMinimalIndex.blockIndex_flatten_index_eq_iff, hS]
  · have hne : blockIndex C (B.index i x) ≠ blockIndex C (B.index j y) := by
      intro h
      have hc : blockIndex B (B.index i x) = blockIndex B (B.index j y) := by
        apply (blockIndex_eq_iff_cut_sides B _ _).mpr
        intro k hk
        exact (blockIndex_eq_iff_cut_sides C _ _).mp h k (hBC hk)
      rw [blockIndex_index, blockIndex_index] at hc
      exact hij hc
    exact iff_of_false (ProductLeviMinimalIndex.blockIndex_flatten_index_ne B S hij x y) hne

/-- Refinements are exactly the finer shapes, expressed by inclusion of cuts. -/
def refinementCutsEquiv (B : BlockShape n) :
    BlockRefinement B ≃ {C : BlockShape n // B.cuts ⊆ C.cuts} :=
  Equiv.ofBijective (fun S => ⟨B.flatten S, cuts_subset_flatten B S⟩) (by
    constructor
    · intro S R h
      exact flatten_refinement_injective B (congrArg Subtype.val h)
    · rintro ⟨C, hC⟩
      obtain ⟨S, hS⟩ := exists_refinement_of_cuts_subset B C hC
      exact ⟨S, Subtype.ext hS⟩)

@[simp] theorem refinementCutsEquiv_val (B : BlockShape n) (S : BlockRefinement B) :
    (refinementCutsEquiv B S).val = B.flatten S := rfl

end Langlands.Aubert
