import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Finite sets of coset representatives

A compact additive subgroup `K` of a topological additive group contains a finite set `T`
of elements that are pairwise incongruent modulo an open subgroup `L` and such that every
element of `K` is congruent modulo `L` to some element of `T`. For an `L`-periodic function
`Φ` whose support is covered by `T + L`, the sum `Σ_(t ∈ T, t ≡ y) Φ(t)` equals `Φ(y)`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

universe uV

variable {V : Type uV} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]

/-- Finite representatives of `K` modulo an open subgroup `L`. -/
theorem exists_finset_addCosetReps (K L : AddSubgroup V) (hK : IsCompact (K : Set V))
    (hL : IsOpen (L : Set V)) :
    ∃ T : Finset V, (T : Set V) ⊆ K ∧
      (∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ L → t = t') ∧
      ∀ v ∈ K, ∃ t ∈ T, v - t ∈ L := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let H : AddSubgroup K := L.addSubgroupOf K
  have hH : IsOpen (H : Set K) := AddSubgroup.addSubgroupOf_isOpen K L hL
  have : Finite (K ⧸ H) := AddSubgroup.quotient_finite_of_isOpen H hH
  have : Fintype (K ⧸ H) := Fintype.ofFinite _
  set T : Finset V := Finset.univ.image fun q : K ⧸ H => ((Quotient.out q : K) : V) with hT
  have hmem : ∀ x, x ∈ T ↔ ∃ q : K ⧸ H, ((Quotient.out q : K) : V) = x := by
    intro x
    simp [hT]
  refine ⟨T, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨q, rfl⟩ := (hmem x).1 hx
    exact (Quotient.out q).2
  · intro t ht t' ht' hd
    obtain ⟨q, rfl⟩ := (hmem t).1 ht
    obtain ⟨q', rfl⟩ := (hmem t').1 ht'
    have hq : q = q' := by
      rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q']
      apply QuotientAddGroup.eq.mpr
      rw [AddSubgroup.mem_addSubgroupOf]
      have : (((-Quotient.out q + Quotient.out q' : K)) : V) =
          -(((Quotient.out q : K) : V) - ((Quotient.out q' : K) : V)) := by
        push_cast; abel
      rw [this]
      exact L.neg_mem hd
    rw [hq]
  · intro v hv
    set q : K ⧸ H := QuotientAddGroup.mk ⟨v, hv⟩ with hq
    refine ⟨((Quotient.out q : K) : V), (hmem _).2 ⟨q, rfl⟩, ?_⟩
    have h := QuotientAddGroup.out_eq' q
    rw [hq, QuotientAddGroup.eq] at h
    rw [AddSubgroup.mem_addSubgroupOf] at h
    have : (((-Quotient.out q + ⟨v, hv⟩ : K)) : V) = v - ((Quotient.out q : K) : V) := by
      push_cast; abel
    rw [this] at h
    exact h

section Sum

variable {V' : Type*} [AddCommGroup V'] {M : Type*} [AddCommMonoid M]

open Classical in
/-- For `L`-periodic `Φ` with support covered by `T + L` and `T` pairwise incongruent modulo
`L`, the sum of `Φ` over the elements of `T` congruent to `y` is `Φ(y)`. -/
theorem sum_reps_eq (L : AddSubgroup V') (Φ : V' → M)
    (hΦ : ∀ z l, l ∈ L → Φ (z + l) = Φ z) (T : Finset V')
    (hT : ∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ L → t = t')
    (hcov : ∀ y, Φ y ≠ 0 → ∃ t ∈ T, y - t ∈ L) (y : V') :
    ∑ t ∈ T, (if t - y ∈ L then Φ t else 0) = Φ y := by
  by_cases h : ∃ t ∈ T, t - y ∈ L
  · obtain ⟨t₀, ht₀, hty⟩ := h
    rw [Finset.sum_eq_single t₀]
    · simp only [hty, ↓reduceIte]
      have := hΦ y (t₀ - y) hty
      rwa [add_sub_cancel] at this
    · intro t ht hne
      have hnot : t - y ∉ L := by
        intro htL
        apply hne
        apply hT t ht t₀ ht₀
        have := L.sub_mem htL hty
        rwa [sub_sub_sub_cancel_right] at this
      simp only [hnot, ↓reduceIte]
    · intro h; exact absurd ht₀ h
  · push Not at h
    rw [Finset.sum_eq_zero fun t ht => by simp only [h t ht, ↓reduceIte]]
    by_contra hy
    obtain ⟨t, ht, hyt⟩ := hcov y (Ne.symm hy)
    apply h t ht
    have := L.neg_mem hyt
    rwa [neg_sub] at this

end Sum

end Langlands.RankinSelberg.HighlyRamified
