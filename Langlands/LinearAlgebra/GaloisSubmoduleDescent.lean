import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Span.Basic

/-! # Infinite-Galois descent of coefficient-stable subspaces -/

noncomputable section

universe u v

namespace Langlands.LinearAlgebra.GaloisSubmoduleDescent

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {ι : Type v}

/-- Extend each coefficient of a finitely supported vector. -/
def extend : (ι →₀ k) →ₗ[k] (ι →₀ K) :=
  Finsupp.mapRange.linearMap (Algebra.linearMap k K)

@[simp] theorem extend_apply (x : ι →₀ k) (i : ι) :
    extend (K := K) x i = algebraMap k K (x i) := rfl

/-- Apply a field automorphism to all coefficients. -/
def conjugate (σ : K ≃ₐ[k] K) (x : ι →₀ K) : ι →₀ K :=
  Finsupp.mapRange σ (map_zero σ) x

@[simp] theorem conjugate_apply (σ : K ≃ₐ[k] K) (x : ι →₀ K) (i : ι) :
    conjugate σ x i = σ (x i) := rfl

/-- A nonzero stable subspace has a fixed vector supported in any given nonzero vector. -/
theorem exists_fixed_supported
    (W : Submodule K (ι →₀ K))
    (hW : ∀ (σ : K ≃ₐ[k] K) (x : ι →₀ K), x ∈ W → conjugate σ x ∈ W)
    (x : ι →₀ K) (hx : x ∈ W) (hne : x ≠ 0) :
    ∃ (y : ι →₀ K) (j : ι), y ∈ W ∧ y.support ⊆ x.support ∧ y j = 1 ∧
      ∀ σ : K ≃ₐ[k] K, conjugate σ y = y := by
  classical
  let P : ℕ → Prop := fun n => ∃ z : ι →₀ K,
    z ∈ W ∧ z ≠ 0 ∧ z.support ⊆ x.support ∧ z.support.card = n
  have hex : ∃ n, P n := ⟨x.support.card, x, hx, hne, Finset.Subset.refl _, rfl⟩
  obtain ⟨z, hz, hz0, hzx, hzc⟩ := Nat.find_spec hex
  obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hz0
  have hzj : z j ≠ 0 := Finsupp.mem_support_iff.mp hj
  let y : ι →₀ K := (z j)⁻¹ • z
  have hyW : y ∈ W := W.smul_mem _ hz
  have hyj : y j = 1 := by simp [y, hzj]
  have hys : y.support ⊆ z.support := Finsupp.support_smul
  refine ⟨y, j, hyW, hys.trans hzx, hyj, ?_⟩
  intro σ
  apply sub_eq_zero.mp
  by_contra hdiff
  let d : ι →₀ K := conjugate σ y - y
  have hdW : d ∈ W := W.sub_mem (hW σ y hyW) hyW
  have hds : d.support ⊆ z.support.erase j := by
    intro i hi
    have hdi : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
    have hij : i ≠ j := by
      intro hij
      subst i
      exact hdi (by simp [d, hyj])
    refine Finset.mem_erase.mpr ⟨hij, ?_⟩
    by_contra hiz
    have hyi : y i = 0 := Finsupp.notMem_support_iff.mp (fun hi => hiz (hys hi))
    exact hdi (by simp [d, hyi])
  have hdlt : d.support.card < Nat.find hex := by
    rw [← hzc]
    exact (Finset.card_le_card hds).trans_lt (Finset.card_erase_lt_of_mem hj)
  have hdn : P d.support.card :=
    ⟨d, hdW, hdiff, (hds.trans (Finset.erase_subset _ _)).trans hzx, rfl⟩
  exact (Nat.find_min hex hdlt) hdn

variable [IsGalois k K]

/-- A fixed finitely supported vector has coefficients in the ground field. -/
theorem exists_extend_of_fixed (x : ι →₀ K)
    (hx : ∀ σ : K ≃ₐ[k] K, conjugate σ x = x) :
    ∃ y : ι →₀ k, extend y = x := by
  have hc : ∀ i, x i ∈ Set.range (algebraMap k K) := by
    intro i
    apply (InfiniteGalois.mem_range_algebraMap_iff_fixed (x i)).mpr
    intro σ
    exact congrArg (fun v : ι →₀ K => v i) (hx σ)
  have hr : x ∈ Set.range (Finsupp.mapRange (algebraMap k K) (map_zero _)) := by
    rw [Finsupp.range_mapRange]
    exact hc
  exact hr

/-- Every stable subspace is spanned over the extension by its ground-field vectors. -/
theorem eq_span_ground_vectors
    (W : Submodule K (ι →₀ K))
    (hW : ∀ (σ : K ≃ₐ[k] K) (x : ι →₀ K), x ∈ W → conjugate σ x ∈ W) :
    W = Submodule.span K {x | ∃ y : ι →₀ k, extend y = x ∧ x ∈ W} := by
  classical
  apply le_antisymm
  · intro x hx
    induction hn : x.support.card using Nat.strong_induction_on generalizing x with
    | h n ih =>
      by_cases hx0 : x = 0
      · subst x
        exact Submodule.zero_mem _
      obtain ⟨y, j, hyW, hys, hyj, hyfixed⟩ := exists_fixed_supported W hW x hx hx0
      obtain ⟨y₀, hy₀⟩ := exists_extend_of_fixed y hyfixed
      have hyspan : y ∈ Submodule.span K {x | ∃ y : ι →₀ k, extend y = x ∧ x ∈ W} :=
        Submodule.subset_span ⟨y₀, hy₀, hyW⟩
      let z := x - x j • y
      have hzW : z ∈ W := W.sub_mem hx (W.smul_mem _ hyW)
      have hjx : j ∈ x.support := hys (Finsupp.mem_support_iff.mpr (by simp [hyj]))
      have hzs : z.support ⊆ x.support.erase j := by
        intro i hi
        have hzi : z i ≠ 0 := Finsupp.mem_support_iff.mp hi
        have hij : i ≠ j := by
          intro hij
          subst i
          exact hzi (by simp [z, hyj])
        refine Finset.mem_erase.mpr ⟨hij, ?_⟩
        by_contra hix
        have hxi : x i = 0 := Finsupp.notMem_support_iff.mp hix
        have hyi : y i = 0 := Finsupp.notMem_support_iff.mp (fun hi => hix (hys hi))
        exact hzi (by simp [z, hxi, hyi])
      have hzlt : z.support.card < n := by
        rw [← hn]
        exact (Finset.card_le_card hzs).trans_lt (Finset.card_erase_lt_of_mem hjx)
      have hzspan := ih z.support.card hzlt hzW rfl
      have hxsum : x = z + x j • y := by simp [z]
      rw [hxsum]
      exact Submodule.add_mem _ hzspan (Submodule.smul_mem _ _ hyspan)
  · apply Submodule.span_le.mpr
    rintro x ⟨y, hy, hx⟩
    exact hx

end Langlands.LinearAlgebra.GaloisSubmoduleDescent
