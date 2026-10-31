import Langlands.Representation.Classification.UniformRefinementCoordinates
import Langlands.Representation.Classification.TwoSourceShuffleLabels
import Langlands.Representation.Classification.TwoSegmentSocleShuffleJacquetStatement
import Langlands.Representation.CuspidalSupport.MinimalJacquetProof

/-! Actual flattened block conjugacy and two-run shuffle exponents. -/

noncomputable section

namespace Langlands.Classification.ShuffleRefinement

open GeneralLinear Geometric CuspidalSupport

section BlockCoordinates

variable {K : Type*} [Field K]
variable {m r : ℕ} (hr : 0 < r)
variable (B : BlockShape (m * r)) (w : Equiv.Perm (Fin (m * r)))
variable (S : BlockRefinement B)
variable (hS : sourceLevi K B (BlockShape.uniform m r hr) w = refinedLevi K B S)

include hS in
theorem refinementTargetIndex_sigma_surjective :
    Function.Surjective (fun q : (j : Fin B.length) × Fin (S j).length =>
      refinementTargetIndex hr B w S q.1 q.2) := by
  intro t
  let C := BlockShape.uniform m r hr
  obtain ⟨⟨j, a⟩, ha⟩ := B.indexEquiv.surjective (w.symm (C.index t ⟨0, hr⟩))
  obtain ⟨⟨i, b⟩, hb⟩ := (S j).indexEquiv.surjective a
  have hx : w (B.index j ((S j).index i b)) = C.index t ⟨0, hr⟩ :=
    (congrArg w ((congrArg (B.index j) hb).trans ha)).trans (w.apply_symm_apply _)
  have hl := (sourceBlockEmbedding B C w S hS j i b).property
  change blockIndex C (w (B.index j ((S j).index i b))) =
    refinementTargetIndex hr B w S j i at hl
  rw [hx] at hl
  exact ⟨⟨j, i⟩, hl.symm.trans (blockIndex_index C t _)⟩

include hS in
theorem refinementTargetIndex_sigma_injective (hdiv : ∀ j i, r ∣ (S j).size i) :
    Function.Injective (fun q : (j : Fin B.length) × Fin (S j).length =>
      refinementTargetIndex hr B w S q.1 q.2) := by
  rintro ⟨j, i⟩ ⟨k, l⟩ he
  have hj := inverse_same_source_block hr B w S hS hdiv
    (w (B.index j ((S j).index i ⟨0, (S j).positive i⟩)))
    (w (B.index k ((S k).index l ⟨0, (S k).positive l⟩))) he
  simp only [Equiv.symm_apply_apply, blockIndex_index] at hj
  subst k
  have hi := refinementTargetIndex_injective hr B w S hS j he
  change i = l at hi
  subst l
  rfl

/-- Every target block corresponds to exactly one source refinement piece. -/
def refinementBlockEquiv (hdiv : ∀ j i, r ∣ (S j).size i) :
    ((j : Fin B.length) × Fin (S j).length) ≃ Fin m :=
  Equiv.ofBijective (fun q => refinementTargetIndex hr B w S q.1 q.2)
    ⟨refinementTargetIndex_sigma_injective hr B w S hS hdiv,
      refinementTargetIndex_sigma_surjective hr B w S hS⟩

include hS in
theorem blockIndex_apply_flatten_index
    (k : Fin (B.flatten S).length) (a : Fin ((B.flatten S).size k)) :
    blockIndex (BlockShape.uniform m r hr) (w ((B.flatten S).index k a)) =
      refinementTargetIndex hr B w S
        ((B.flattenBlockEquiv S).symm k).1 ((B.flattenBlockEquiv S).symm k).2 := by
  rw [B.flatten_index S k a]
  exact (sourceBlockEmbedding B (BlockShape.uniform m r hr) w S hS
    ((B.flattenBlockEquiv S).symm k).1 ((B.flattenBlockEquiv S).symm k).2 a).property

include hS in
/-- Divisible source pieces give actual conjugacy of the flattened and target
Levi subgroups. No minimality is required for this conclusion. -/
theorem conjugatesLevi_flatten_uniform (hdiv : ∀ j i, r ∣ (S j).size i) :
    ConjugatesLevi (F := K) (B.flatten S) (BlockShape.uniform m r hr) w := by
  rw [TotalConjugatingCount.conjugatesLevi_iff]
  intro a b
  obtain ⟨⟨i, x⟩, rfl⟩ := (B.flatten S).indexEquiv.surjective a
  obtain ⟨⟨j, y⟩, rfl⟩ := (B.flatten S).indexEquiv.surjective b
  change
    blockIndex (B.flatten S) ((B.flatten S).index i x) =
        blockIndex (B.flatten S) ((B.flatten S).index j y) ↔
      blockIndex (BlockShape.uniform m r hr) (w ((B.flatten S).index i x)) =
        blockIndex (BlockShape.uniform m r hr) (w ((B.flatten S).index j y))
  rw [blockIndex_index, blockIndex_index,
    blockIndex_apply_flatten_index hr B w S hS i x,
    blockIndex_apply_flatten_index hr B w S hS j y]
  constructor
  · rintro rfl
    rfl
  · intro he
    apply (B.flattenBlockEquiv S).symm.injective
    exact (refinementBlockEquiv hr B w S hS hdiv).injective he

end BlockCoordinates

section TwoSource

variable {K : Type*} [Field K]
variable {m₀ m₁ r : ℕ} (hr : 0 < r)
variable (B : BlockShape ((m₀ + m₁) * r)) (h₂ : B.length = 2)
variable (h₀ : B.size (Fin.cast h₂.symm 0) = m₀ * r)
variable (h₁ : B.size (Fin.cast h₂.symm 1) = m₁ * r)
variable (w : Equiv.Perm (Fin ((m₀ + m₁) * r))) (S : BlockRefinement B)
variable (hS : sourceLevi K B (BlockShape.uniform (m₀ + m₁) r hr) w = refinedLevi K B S)
variable (hw : IsMinimalRepresentative B (BlockShape.uniform (m₀ + m₁) r hr) w)

/-- The actual shuffle subset associated to divisible source refinements. -/
def refinementShuffle (hdiv : ∀ j i, r ∣ (S j).size i) :
    {A : Finset (Fin (m₀ + m₁)) // A.card = m₀} :=
  wholeTargetEquivShuffles hr B h₂ h₀ h₁
    ⟨⟨w, hw⟩, inverse_same_source_block hr B w S hS hdiv⟩

theorem refinementShuffle_val (hdiv : ∀ j i, r ∣ (S j).size i) :
    (refinementShuffle hr B h₂ h₀ h₁ w S hS hw hdiv).val =
      sourceTargetBlocks hr B w (Fin.cast h₂.symm 0) := by
  classical
  have hs : (refinementShuffle hr B h₂ h₀ h₁ w S hS hw hdiv).val =
      binarySubset (fun t => Fin.cast h₂ (targetBlockLabel B
        (BlockShape.uniform (m₀ + m₁) r hr) w t)) := rfl
  rw [hs]
  ext t
  constructor
  · intro ht
    exact (@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _).mpr
      ⟨Finset.mem_univ _,
      congrArg (Fin.cast h₂.symm) (Finset.mem_filter.mp ht).2⟩
  · intro ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      congrArg (Fin.cast h₂)
        ((@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _).mp ht).2⟩

theorem refinementShuffle_compl (hdiv : ∀ j i, r ∣ (S j).size i) :
    (refinementShuffle hr B h₂ h₀ h₁ w S hS hw hdiv).valᶜ =
      sourceTargetBlocks hr B w (Fin.cast h₂.symm 1) := by
  classical
  rw [refinementShuffle_val hr B h₂ h₀ h₁ w S hS hw hdiv]
  ext t
  simp only [sourceTargetBlocks, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ,
    true_and]
  let j := targetBlockLabel B (BlockShape.uniform (m₀ + m₁) r hr) w t
  change j ≠ Fin.cast h₂.symm 0 ↔ j = Fin.cast h₂.symm 1
  have hjlt : j.val < 2 := h₂ ▸ j.isLt
  constructor
  · intro hj
    apply Fin.ext
    have hj0 : j.val ≠ 0 := fun he => hj (Fin.ext he)
    change j.val = 1
    omega
  · intro hj he
    have he' := congrArg Fin.val (he.symm.trans hj)
    simp at he'

include hS hw in
/-- At a first-source target block the shuffle exponent is the first starting
exponent plus the source piece number. -/
theorem shuffleExponent_refinementTargetIndex_zero
    (hdiv : ∀ j i, r ∣ (S j).size i) (a₀ a₁ : ℝ)
    (i : Fin (S (Fin.cast h₂.symm 0)).length) :
    shuffleExponent (refinementShuffle hr B h₂ h₀ h₁ w S hS hw hdiv).val a₀ a₁
      (refinementTargetIndex hr B w S (Fin.cast h₂.symm 0) i) =
        a₀ + (i.val : ℝ) := by
  classical
  rw [refinementShuffle_val hr B h₂ h₀ h₁ w S hS hw hdiv]
  have hi : refinementTargetIndex hr B w S (Fin.cast h₂.symm 0) i ∈
      sourceTargetBlocks hr B w (Fin.cast h₂.symm 0) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      refinementTargetIndex_label hr B w S hS hw _ i (hdiv _ i)⟩
  rw [shuffleExponent, ite_eq_left hi,
    card_sourceTargetBlocks_before hr B w S hS hw hdiv _ i]

include hS hw in
/-- At a second-source target block the complement count gives the second
starting exponent plus the source piece number. -/
theorem shuffleExponent_refinementTargetIndex_one
    (hdiv : ∀ j i, r ∣ (S j).size i) (a₀ a₁ : ℝ)
    (i : Fin (S (Fin.cast h₂.symm 1)).length) :
    shuffleExponent (refinementShuffle hr B h₂ h₀ h₁ w S hS hw hdiv).val a₀ a₁
      (refinementTargetIndex hr B w S (Fin.cast h₂.symm 1) i) =
        a₁ + (i.val : ℝ) := by
  classical
  have hi : refinementTargetIndex hr B w S (Fin.cast h₂.symm 1) i ∈
      sourceTargetBlocks hr B w (Fin.cast h₂.symm 1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      refinementTargetIndex_label hr B w S hS hw _ i (hdiv _ i)⟩
  have hn : refinementTargetIndex hr B w S (Fin.cast h₂.symm 1) i ∉
      (refinementShuffle hr B h₂ h₀ h₁ w S hS hw hdiv).val := by
    rw [← refinementShuffle_compl hr B h₂ h₀ h₁ w S hS hw hdiv] at hi
    exact Finset.mem_compl.mp hi
  rw [shuffleExponent, ite_eq_right hn,
    refinementShuffle_compl hr B h₂ h₀ h₁ w S hS hw hdiv,
    card_sourceTargetBlocks_before hr B w S hS hw hdiv _ i]

end TwoSource

end Langlands.Classification.ShuffleRefinement
