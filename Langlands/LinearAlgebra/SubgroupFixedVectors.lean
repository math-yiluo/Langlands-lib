import Langlands.LinearAlgebra.GaloisSubmoduleDescent

/-! # Fixed vectors for arbitrary subgroups of coefficient automorphisms -/

noncomputable section

universe u v

namespace Langlands.LinearAlgebra.SubgroupFixedVectors

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {ι : Type v}

open GaloisSubmoduleDescent

/-- The extension-field span of the subgroup-fixed vectors in a subspace. -/
def fixedVectorSpan (H : Subgroup (K ≃ₐ[k] K)) (W : Submodule K (ι →₀ K)) :
    Submodule K (ι →₀ K) :=
  Submodule.span K {x | x ∈ W ∧ ∀ σ ∈ H, conjugate σ x = x}

/-- Minimal support and normalization produce a subgroup-fixed nonzero vector,
without assuming the subgroup finite or the extension Galois. -/
theorem exists_fixed_supported
    (H : Subgroup (K ≃ₐ[k] K)) (W : Submodule K (ι →₀ K))
    (hW : ∀ σ ∈ H, ∀ x ∈ W, conjugate σ x ∈ W)
    (x : ι →₀ K) (hx : x ∈ W) (hne : x ≠ 0) :
    ∃ (y : ι →₀ K) (j : ι), y ∈ W ∧ y.support ⊆ x.support ∧ y j = 1 ∧
      ∀ σ ∈ H, conjugate σ y = y := by
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
  intro σ hσ
  apply sub_eq_zero.mp
  by_contra hdiff
  let d : ι →₀ K := conjugate σ y - y
  have hdW : d ∈ W := W.sub_mem (hW σ hσ y hyW) hyW
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

/-- A subgroup-invariant subspace is spanned by its subgroup-fixed vectors. -/
theorem eq_fixedVectorSpan
    (H : Subgroup (K ≃ₐ[k] K)) (W : Submodule K (ι →₀ K))
    (hW : ∀ σ ∈ H, ∀ x ∈ W, conjugate σ x ∈ W) :
    W = fixedVectorSpan H W := by
  classical
  apply le_antisymm
  · intro x hx
    induction hn : x.support.card using Nat.strong_induction_on generalizing x with
    | h n ih =>
      by_cases hx0 : x = 0
      · subst x
        exact Submodule.zero_mem _
      obtain ⟨y, j, hyW, hys, hyj, hyfixed⟩ := exists_fixed_supported H W hW x hx hx0
      have hyspan : y ∈ fixedVectorSpan H W := Submodule.subset_span ⟨hyW, hyfixed⟩
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
    exact fun _ hx => hx.1

variable [Fintype ι]

/-- A nonzero invariant finite-coordinate space has a subgroup-fixed vector with
some coordinate equal to one. -/
theorem exists_fixed_pi
    (H : Subgroup (K ≃ₐ[k] K)) (W : Submodule K (ι → K))
    (hW : ∀ σ ∈ H, ∀ x ∈ W, (fun i => σ (x i)) ∈ W)
    (hne : W ≠ ⊥) :
    ∃ (y : ι → K) (j : ι), y ∈ W ∧ y j = 1 ∧
      ∀ σ ∈ H, (fun i => σ (y i)) = y := by
  let e := Finsupp.linearEquivFunOnFinite K K ι
  let W' := W.comap e.toLinearMap
  have hW' (σ : K ≃ₐ[k] K) (hσ : σ ∈ H) (x : ι →₀ K) (hx : x ∈ W') :
      conjugate σ x ∈ W' := hW σ hσ (e x) hx
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hne
  have hx' : e.symm x ∈ W' := by
    change e (e.symm x) ∈ W
    simpa only [LinearEquiv.apply_symm_apply] using hx
  have hx0' : e.symm x ≠ 0 := by
    intro h
    apply hx0
    simpa only [LinearEquiv.apply_symm_apply, map_zero] using congrArg e h
  obtain ⟨y, j, hyW, _, hyj, hyfixed⟩ := exists_fixed_supported H W' hW' _ hx' hx0'
  refine ⟨e y, j, hyW, hyj, ?_⟩
  intro σ hσ
  exact congrArg e (hyfixed σ hσ)

end Langlands.LinearAlgebra.SubgroupFixedVectors
