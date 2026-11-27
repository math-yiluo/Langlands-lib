import Langlands.LinearAlgebra.ArthurCombinatoricsAlternating
import Mathlib.Basic.Complex.Basic

/-! # Alternation of the cutoffs in Arthur's constant-term formula -/

noncomputable section

namespace Langlands.ArthurCombinatorics

open scoped Classical

/-- In the constant-term expansion, the free simple roots can be inserted
or deleted without changing the accompanying integral. If the evaluation
with coefficients `c` is positive, either all cutoffs vanish or one free root
has positive weight. In the latter case insertion pairs terms with opposite signs.
The neutral roots are the ones in the Levi intersection. -/
theorem alternatingCutoff_eq_zero {ι : Type*} [DecidableEq ι] (Δ free neutral : Finset ι)
    (hfree : free ⊆ Δ) (hneutral : neutral ⊆ Δ) (hdis : Disjoint free neutral)
    (c weight : ι → ℝ) (f : Finset ι → ℂ)
    (hcoeff₁ : ∀ a ∈ free, 0 ≤ c a)
    (hcoeff₂ : ∀ a ∈ neutral, c a = 0)
    (hcoeff₃ : ∀ a ∈ Δ, a ∉ free ∪ neutral → c a ≤ 0)
    (hf : ∀ S ∈ (free ∪ neutral).powerset, f S = f (S ∩ neutral))
    (hpos : 0 < ∑ a ∈ Δ, c a * weight a) :
    ∑ S ∈ (free ∪ neutral).powerset,
      (-1 : ℂ) ^ (Δ.card - S.card) *
        (if ∀ a ∈ Δ \ S, 0 < weight a then f S else 0) = 0 := by
  by_cases hsupport : ∃ S ∈ (free ∪ neutral).powerset, ∀ a ∈ Δ \ S, 0 < weight a
  · obtain ⟨S₀, hS₀, hcut⟩ := hsupport
    have hpositive : ∃ a ∈ free, 0 < weight a := by
      by_contra! h
      apply (not_lt_of_ge _ hpos)
      apply Finset.sum_nonpos
      intro a ha
      by_cases haf : a ∈ free
      · exact mul_nonpos_of_nonneg_of_nonpos (hcoeff₁ a haf) (h a haf)
      by_cases han : a ∈ neutral
      · simp only [hcoeff₂ a han, zero_mul, le_rfl]
      have hna : a ∉ free ∪ neutral := by simp only [Finset.mem_union, haf, han, or_self, not_false_eq_true]
      have hnot : a ∉ S₀ := fun hmem => hna (Finset.mem_powerset.mp hS₀ hmem)
      exact mul_nonpos_of_nonpos_of_nonneg (hcoeff₃ a ha hna)
        (hcut a (Finset.mem_sdiff.mpr ⟨ha, hnot⟩)).le
    obtain ⟨a, ha, hwa⟩ := hpositive
    let allowed := free ∪ neutral
    have ha' : a ∈ allowed := Finset.mem_union_left _ ha
    have han : a ∉ neutral := fun h => (Finset.disjoint_left.mp hdis ha h).elim
    have hsubl : allowed ⊆ Δ := Finset.union_subset hfree hneutral
    let t (S : Finset ι) : ℂ := (-1 : ℂ) ^ (Δ.card - S.card) *
      (if ∀ x ∈ Δ \ S, 0 < weight x then f S else 0)
    change (∑ S ∈ allowed.powerset, t S) = 0
    have hsplit : allowed = insert a (allowed.erase a) := (Finset.insert_erase ha').symm
    have hnotMem : ∀ S ∈ (allowed.erase a).powerset, a ∉ S :=
      fun _ hS => Finset.notMem_of_mem_powerset_of_notMem hS (Finset.notMem_erase a allowed)
    have hinj : Set.InjOn (insert a) (↑(allowed.erase a).powerset : Set (Finset ι)) := by
      intro S hS R hR hSR
      exact Finset.insert_erase_invOn.2.injOn (hnotMem S hS) (hnotMem R hR) hSR
    have hdisjoint : Disjoint (allowed.erase a).powerset ((allowed.erase a).powerset.image (insert a)) := by
      apply Finset.disjoint_left.mpr
      intro S hS himage
      obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp himage
      exact hnotMem _ hS (Finset.mem_insert_self a R)
    rw [hsplit, Finset.powerset_insert, Finset.sum_union hdisjoint, Finset.sum_image hinj,
      ← Finset.sum_add_distrib]
    ·
      refine Finset.sum_eq_zero fun S hS => ?_
      have hS₁ := (Finset.mem_powerset.mp hS).trans (Finset.erase_subset a allowed)
      have hnot : a ∉ S := hnotMem S hS
      have hins : insert a S ⊆ allowed := Finset.insert_subset ha' hS₁
      have hinter : insert a S ∩ neutral = S ∩ neutral := by
        ext x
        by_cases hxa : x = a
        · subst x
          simp [han]
        · simp [hxa]
      have hsame : f (insert a S) = f S :=
        (hf _ (Finset.mem_powerset.mpr hins)).trans (by
          rw [hinter]
          exact (hf _ (Finset.mem_powerset.mpr hS₁)).symm)
      have hw : (∀ x ∈ Δ \ insert a S, 0 < weight x) ↔ (∀ x ∈ Δ \ S, 0 < weight x) := by
        constructor
        · intro h x hx
          by_cases hxa : x = a
          · exact hxa.symm ▸ hwa
          · refine h x (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1, ?_⟩)
            simpa [hxa] using (Finset.mem_sdiff.mp hx).2
        · exact fun h x hx => h x (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1,
            fun hxS => (Finset.mem_sdiff.mp hx).2 (Finset.mem_insert_of_mem hxS)⟩)
      have hcard : Δ.card - S.card = Δ.card - (insert a S).card + 1 := by
        have hle := Finset.card_le_card (hins.trans hsubl)
        rw [Finset.card_insert_of_notMem hnot] at hle ⊢
        omega
      change t S + t (insert a S) = 0
      simp only [t, hw, hsame]
      rw [hcard, pow_succ]
      ring
  · refine Finset.sum_eq_zero fun S hS => ?_
    have h : ¬ ∀ a ∈ Δ \ S, 0 < weight a := fun hw => hsupport ⟨S, hS, hw⟩
    rw [ite_eq_right h, mul_zero]

end Langlands.ArthurCombinatorics
