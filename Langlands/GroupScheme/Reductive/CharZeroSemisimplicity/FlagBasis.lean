import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! # Bases adapted to a finite decreasing flag of subspaces -/

noncomputable section

open Module

namespace Langlands.LinearAlgebra

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- One downward step of the construction of a flag-adapted linearly independent
family: extend a family adapted to the steps above `t` to one adapted to the steps
from `t` on, giving the new vectors level `t`. -/
theorem exists_linearIndepOn_flag_step (F : ℕ → Submodule k V) (hF : Antitone F) (t : ℕ)
    (s : Set V) (e : V → ℕ) (hs : LinearIndepOn k id s) (hse : ∀ v ∈ s, t + 1 ≤ e v)
    (hspan : ∀ t', t + 1 ≤ t' → F t' = Submodule.span k (s ∩ {v | t' ≤ e v})) :
    ∃ (s' : Set V) (e' : V → ℕ), LinearIndepOn k id s' ∧ (∀ v ∈ s', t ≤ e' v) ∧
      ∀ t', t ≤ t' → F t' = Submodule.span k (s' ∩ {v | t' ≤ e' v}) := by
  classical
  have hs1 : F (t + 1) = Submodule.span k s := by
    rw [hspan (t + 1) le_rfl]
    congr 1
    ext w
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h => h.1, fun h => ⟨h, hse w h⟩⟩
  have hsF : s ⊆ F t := by
    intro v hv
    exact hF (Nat.le_succ t) (hs1 ▸ Submodule.subset_span hv)
  obtain ⟨b, hbF, hsb, hFb, hb⟩ := exists_linearIndepOn_id_extension hs hsF
  refine ⟨b, fun v => if v ∈ s then e v else t, hb, ?_, ?_⟩
  · intro v _
    simp only
    split_ifs with h
    · exact (Nat.le_succ t).trans (hse v h)
    · exact le_rfl
  · intro t' ht'
    rcases ht'.lt_or_eq with hlt | rfl
    · rw [hspan t' hlt]
      congr 1
      ext v
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hv, hle⟩
        exact ⟨hsb hv, by simp only [hv, ↓reduceIte]; exact hle⟩
      · rintro ⟨hv, hle⟩
        by_cases hvs : v ∈ s
        · simp only [hvs, ↓reduceIte] at hle
          exact ⟨hvs, hle⟩
        · simp only [hvs, ↓reduceIte] at hle
          omega
    · have hb' : b ∩ {v | t ≤ (if v ∈ s then e v else t)} = b := by
        apply Set.inter_eq_left.mpr
        intro v _
        simp only [Set.mem_ofPred_eq]
        split_ifs with h
        · exact (Nat.le_succ t).trans (hse v h)
        · exact le_rfl
      rw [hb']
      apply le_antisymm
      · exact fun x hx => hFb hx
      · exact Submodule.span_le.mpr hbF

/-- A decreasing chain of subspaces reaching zero admits a linearly independent
family with a level function such that every step of the chain is spanned by the
vectors of level at least that step. -/
theorem exists_linearIndepOn_flag (F : ℕ → Submodule k V) (hF : Antitone F) (m : ℕ)
    (hm : F m = ⊥) :
    ∃ (s : Set V) (e : V → ℕ), LinearIndepOn k id s ∧
      ∀ t, F t = Submodule.span k (s ∩ {v | t ≤ e v}) := by
  have key : ∀ d t, m ≤ t + d → ∃ (s : Set V) (e : V → ℕ), LinearIndepOn k id s ∧
      (∀ v ∈ s, t ≤ e v) ∧ ∀ t', t ≤ t' → F t' = Submodule.span k (s ∩ {v | t' ≤ e v}) := by
    intro d
    induction d with
    | zero =>
      intro t ht
      refine ⟨∅, fun _ => 0, linearIndepOn_empty k id, fun v hv => hv.elim, fun t' ht' => ?_⟩
      rw [Set.empty_inter, Submodule.span_empty]
      exact eq_bot_iff.mpr (hm ▸ hF (by omega))
    | succ d ih =>
      intro t ht
      obtain ⟨s, e, hs, hse, hspan⟩ := ih (t + 1) (by omega)
      exact exists_linearIndepOn_flag_step F hF t s e hs hse hspan
  obtain ⟨s, e, hs, -, hspan⟩ := key m 0 (by omega)
  exact ⟨s, e, hs, fun t => hspan t (Nat.zero_le t)⟩

/-- A decreasing chain of subspaces of `n → k`, starting at the whole space and
reaching zero, has a basis indexed by `n` and a level function on `n` such that
every step of the chain is spanned by the basis vectors of level at least that
step. -/
theorem exists_basis_flag {n : Type*} [Fintype n] (F : ℕ → Submodule k (n → k))
    (hF : Antitone F) (h0 : F 0 = ⊤) (m : ℕ) (hm : F m = ⊥) :
    ∃ (b : Basis n k (n → k)) (e : n → ℕ),
      ∀ t, F t = Submodule.span k (b '' {i | t ≤ e i}) := by
  classical
  obtain ⟨s, e, hs, hspan⟩ := exists_linearIndepOn_flag F hF m hm
  have hstop : ⊤ ≤ Submodule.span k (Set.range ((↑) : s → (n → k))) := by
    rw [Subtype.range_coe, ← h0, hspan 0]
    exact Submodule.span_mono Set.inter_subset_left
  let b₀ : Basis s k (n → k) := Basis.mk hs.linearIndependent hstop
  let τ := b₀.indexEquiv (Pi.basisFun k n)
  let b := b₀.reindex τ
  have hbapp (i : n) : b i = (τ.symm i : n → k) := by
    simp only [b, b₀, Basis.reindex_apply, Basis.mk_apply, id_eq]
  refine ⟨b, fun i => e (b i), fun t => ?_⟩
  rw [hspan t]
  congr 1
  ext v
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨hv, hle⟩
    refine ⟨τ ⟨v, hv⟩, ?_, ?_⟩
    · rw [hbapp, Equiv.symm_apply_apply]
      exact hle
    · rw [hbapp, Equiv.symm_apply_apply]
  · rintro ⟨i, hi, rfl⟩
    refine ⟨?_, hi⟩
    rw [hbapp]
    exact (τ.symm i).property

/-- In a basis adapted to a flag, an endomorphism moving every step of the flag at
least `d` steps down has vanishing coefficients at the positions `(i, j)` with
`e i < e j + d`. -/
theorem repr_apply_eq_zero_of_flag {n : Type*} (b : Basis n k V) (e : n → ℕ)
    (F : ℕ → Submodule k V) (hb : ∀ t, F t = Submodule.span k (b '' {i | t ≤ e i}))
    (f : V →ₗ[k] V) (d : ℕ) (hf : ∀ t, ∀ v ∈ F t, f v ∈ F (t + d)) (i j : n)
    (hij : e i < e j + d) : b.repr (f (b j)) i = 0 := by
  have hj : b j ∈ F (e j) := by
    rw [hb]
    exact Submodule.subset_span ⟨j, (le_rfl : e j ≤ e j), rfl⟩
  have hfj := hf _ _ hj
  rw [hb, Basis.mem_span_image] at hfj
  by_contra hne
  have := hfj (Finsupp.mem_support_iff.mpr hne)
  simp only [Set.mem_ofPred_eq] at this
  omega

end Langlands.LinearAlgebra
