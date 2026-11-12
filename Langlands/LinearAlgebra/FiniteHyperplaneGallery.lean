import Mathlib.Tactic
import Mathlib.Logic.Relation

/-! # Finite chamber galleries along a rational segment -/

noncomputable section

namespace Langlands.LinearAlgebra.FiniteHyperplaneSegment

/-- An interval contains at most one point of the specified finite set. -/
def SparseInterval (s : Finset ℚ) (a b : ℚ) : Prop :=
  (s.filter (fun t => a < t ∧ t < b)).card ≤ 1

/-- A finite set of breakpoints can be crossed by a finite chain of intervals,
with at most one breakpoint in each interval and none at the chain vertices. -/
theorem reflTransGen_of_sparse_intervals (R : ℚ → ℚ → Prop) (s : Finset ℚ)
    {a b : ℚ} (hab : a < b) (hs : ∀ t ∈ s, a < t ∧ t < b)
    (hstep : ∀ c d, a ≤ c → c < d → d ≤ b → c ∉ s → d ∉ s →
      SparseInterval s c d → R c d) : Relation.ReflTransGen R a b := by
  classical
  induction s using Finset.strongInduction generalizing a b with
  | H s ih =>
    have ha : a ∉ s := fun h => (hs a h).1.false
    have hb : b ∉ s := fun h => (hs b h).2.false
    by_cases hsmall : s.card ≤ 1
    · exact Relation.ReflTransGen.single (hstep a b le_rfl hab le_rfl ha hb
        (le_trans (Finset.card_filter_le _ _) hsmall))
    have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
    let u := s.min' hsne
    have hu : u ∈ s := Finset.min'_mem s hsne
    have htail : (s.erase u).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem hu]
      omega
    let v := (s.erase u).min' htail
    have hv : v ∈ s.erase u := Finset.min'_mem _ _
    have hvu : v ≠ u := (Finset.mem_erase.mp hv).1
    have huv : u < v := lt_of_le_of_ne
      (Finset.min'_le s v (Finset.mem_of_mem_erase hv)) (Ne.symm hvu)
    let c := (u + v) / 2
    have huc : u < c := by dsimp [c]; linarith
    have hcv : c < v := by dsimp [c]; linarith
    have hac : a < c := lt_trans (hs u hu).1 huc
    have hcb : c < b := lt_trans hcv (hs v (Finset.mem_of_mem_erase hv)).2
    have hc : c ∉ s := by
      intro hc
      have hcu : c ≠ u := ne_of_gt huc
      have hcmem : c ∈ s.erase u := Finset.mem_erase.mpr ⟨hcu, hc⟩
      exact (not_le.mpr hcv) (Finset.min'_le _ _ hcmem)
    have hleft : SparseInterval s a c := by
      have hsub : s.filter (fun t => a < t ∧ t < c) ⊆ {u} := by
        intro t ht
        have hts := (Finset.mem_filter.mp ht).1
        have htc := (Finset.mem_filter.mp ht).2.2
        by_contra htu
        have hne : t ≠ u := by simpa using htu
        have hvt : v ≤ t := Finset.min'_le _ _ (Finset.mem_erase.mpr ⟨hne, hts⟩)
        exact (not_le.mpr (lt_trans htc hcv)) hvt
      exact (Finset.card_le_card hsub).trans (by simp)
    have hR : R a c := hstep a c le_rfl hac hcb.le ha hc hleft
    have hrest : Relation.ReflTransGen R c b := by
      apply ih (s.erase u) (Finset.erase_ssubset hu) hcb
      · intro t ht
        have hvt : v ≤ t := Finset.min'_le _ _ ht
        exact ⟨lt_of_lt_of_le hcv hvt, (hs t (Finset.mem_of_mem_erase ht)).2⟩
      · intro d e hcd hde heb hd he hdeSparse
        have hd' : d ∉ s := by
          intro hdmem
          apply hd
          exact Finset.mem_erase.mpr ⟨ne_of_gt (lt_of_lt_of_le huc hcd), hdmem⟩
        have he' : e ∉ s := by
          intro hemem
          apply he
          exact Finset.mem_erase.mpr
            ⟨ne_of_gt (lt_trans (lt_of_lt_of_le huc hcd) hde), hemem⟩
        apply hstep d e (le_trans hac.le hcd) hde heb hd' he'
        have hfilter : s.filter (fun t => d < t ∧ t < e) =
            (s.erase u).filter (fun t => d < t ∧ t < e) := by
          ext t
          simp only [Finset.mem_filter, Finset.mem_erase]
          constructor
          · rintro ⟨hts, hdt, hte⟩
            exact ⟨⟨ne_of_gt (lt_trans (lt_of_lt_of_le huc hcd) hdt), hts⟩, hdt, hte⟩
          · rintro ⟨⟨-, hts⟩, hdt, hte⟩
            exact ⟨hts, hdt, hte⟩
        simpa only [SparseInterval, hfilter] using hdeSparse
    exact (Relation.ReflTransGen.single hR).trans hrest

end Langlands.LinearAlgebra.FiniteHyperplaneSegment
