import Langlands.Representation.Classification.LanglandsData
import Langlands.Group.GL.AdjacentMergeShape

/-! # Permuting segment-product data

The permutation sends a new position to its original label. An adjacent swap
of unlinked segments preserves the precedence ordering.
-/

noncomputable section

namespace Langlands.PadicField.TopologicalData

open CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace SegmentProductDatum

variable {n : ℕ} (d : SegmentProductDatum.{uV, uF} T n)

/-- Relabel the segments and their actual blocks by the same permutation. -/
def permute (σ : Equiv.Perm (Fin d.length)) : SegmentProductDatum.{uV, uF} T n where
  length := d.length
  segments i := d.segments (σ i)
  degree_sum := (Equiv.sum_comp σ (fun i => (d.segments i).degree)).trans d.degree_sum
  blocks i := d.blocks (σ i)

@[simp] theorem permute_length (σ : Equiv.Perm (Fin d.length)) :
    (d.permute σ).length = d.length := rfl

@[simp] theorem permute_segments (σ : Equiv.Perm (Fin d.length)) (i : Fin d.length) :
    (d.permute σ).segments i = d.segments (σ i) := rfl

@[simp] theorem permute_blocks (σ : Equiv.Perm (Fin d.length)) (i : Fin d.length) :
    letI := T.topology
    (d.permute σ).blocks i = d.blocks (σ i) := rfl

@[simp] theorem permute_shape (σ : Equiv.Perm (Fin d.length)) :
    (d.permute σ).shape = d.shape.permute σ := rfl

@[simp] theorem permute_refl : d.permute (Equiv.refl _) = d := rfl

@[simp] theorem permute_permute (σ τ : Equiv.Perm (Fin d.length)) :
    (d.permute σ).permute τ = d.permute (τ.trans σ) := rfl

theorem permute_induced (σ : Equiv.Perm (Fin d.length)) :
    letI := T.topology
    (d.permute σ).induced =
      (T.normalizedProductInductionFunctor (d.shape.permute σ)).obj
        (fun i => d.blocks (σ i)) := rfl

theorem HasSegmentHeads.permute {d : SegmentProductDatum.{uV, uF} T n}
    (h : d.HasSegmentHeads) (σ : Equiv.Perm (Fin d.length)) :
    (d.permute σ).HasSegmentHeads := fun i => h (σ i)

/-- Reindexing retains every original occurrence with its original block. -/
theorem permute_occurrences (σ : Equiv.Perm (Fin d.length)) :
    letI := T.topology
    ∀ i, ∃ h : (d.segments i).degree = ((d.permute σ).segments (σ.symm i)).degree,
      Nonempty ((h ▸ d.blocks i) ≅ (d.permute σ).blocks (σ.symm i)) := by
  let := T.topology
  intro i
  have hi := σ.apply_symm_apply i
  change ∃ h : (d.segments i).degree = (d.segments (σ (σ.symm i))).degree,
    Nonempty ((h ▸ d.blocks i) ≅ d.blocks (σ (σ.symm i)))
  generalize σ (σ.symm i) = k at hi ⊢
  subst k
  exact ⟨rfl, ⟨Iso.refl _⟩⟩

/-- Only the relative order of the swapped adjacent pair can be reversed.
Unlinkage rules out precedence in that pair in either direction. -/
theorem IsPrecedenceOrdered.permute_adjacentSwap
    {d : SegmentProductDatum.{uV, uF} T n} (ho : d.IsPrecedenceOrdered)
    (j : ℕ) (h : j + 1 < d.length)
    (hu : ¬ (d.segments ⟨j, by omega⟩).IsLinked (d.segments ⟨j + 1, h⟩)) :
    (d.permute (d.shape.adjacentSwap j h)).IsPrecedenceOrdered := by
  let a : Fin d.length := ⟨j, by omega⟩
  let b : Fin d.length := ⟨j + 1, h⟩
  change ∀ i k, i < k →
    ¬ (d.segments (Equiv.swap a b i)).Precedes (d.segments (Equiv.swap a b k))
  intro i k hik
  by_cases hp : i = a ∧ k = b
  · rcases hp with ⟨rfl, rfl⟩
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact fun hprec => hu hprec.isLinked.symm
  · apply ho
    simp only [Equiv.swap_apply_def]
    split_ifs <;>
      simp_all only [Fin.lt_def, Fin.ext_iff, a, b, and_self, not_true_eq_false] <;> omega

end SegmentProductDatum
end Langlands.PadicField.TopologicalData
