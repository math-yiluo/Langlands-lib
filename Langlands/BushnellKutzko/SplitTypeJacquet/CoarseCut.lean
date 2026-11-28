import Langlands.BushnellKutzko.SplitTypeJacquet.CoarseFactorization
import Langlands.Representation.Whittaker.UpperUnipotentCoinvariantReduction
import Langlands.Representation.Classification.Supercuspidal

/-! # The coarse corner as a conjugate of a standard two-block unipotent radical

The late-early corner `coarseN F blk j` contains the conjugate of the unipotent radical of the
two-block shape `(b, n - b)`, where `b` is the number of late coordinates, by a permutation
carrying the first `b` coordinates onto the late ones. Nonvanishing of a Jacquet module along a
subgroup passes to every subgroup of it. -/

open Matrix Langlands.GeneralLinear

noncomputable section

namespace Langlands.BushnellKutzko.SplitTypeJacquet

open Langlands.ProductLeviChamber (twoBlock)
open Langlands.Whittaker.UpperUnipotentCoinvariant (isBlockUnipotent_of_mem_cutShape
  cutShape_parabolic_ne_top)

universe uF uG uV

section Monotone

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A nonzero Jacquet module along `N` gives a nonzero Jacquet module along every subgroup of
`N`. -/
theorem not_subsingleton_coinvariants_of_le (ρ : Representation ℂ G V) {N N' : Subgroup G}
    (h : N' ≤ N) (hN : ¬ Subsingleton (Jacquet.Coinvariants ρ N)) :
    ¬ Subsingleton (Jacquet.Coinvariants ρ N') := by
  intro hN'
  apply hN
  let q := Jacquet.mk ρ N
  have hinv : ∀ u : N', q ∘ₗ ρ u.val = q := fun u =>
    LinearMap.ext fun v => Jacquet.mk_apply_subgroup ρ N ⟨u.val, h u.2⟩ v
  refine ⟨fun x y => ?_⟩
  obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ N x
  obtain ⟨w, rfl⟩ := Jacquet.mk_surjective ρ N y
  have hl := Jacquet.lift_mk ρ N' q hinv
  rw [← hl v, ← hl w, Subsingleton.elim (Jacquet.mk ρ N' v) (Jacquet.mk ρ N' w)]

end Monotone

variable {F : Type uF} [Field F] {n : ℕ} {blk : Fin n → ℕ} {j : ℕ}

/-- A matrix agreeing with the identity outside the late-early corner lies in `coarseN`. -/
theorem mem_coarseN_of_entries {g : GL (Fin n) F}
    (hg : ∀ p q, ¬ (j ≤ blk p ∧ ¬ j ≤ blk q) →
      (g : Matrix (Fin n) (Fin n) F) p q = (1 : Matrix (Fin n) (Fin n) F) p q) :
    g ∈ coarseN F blk j := by
  refine ⟨Multiplicative.ofAdd (fun a b => (g : Matrix (Fin n) (Fin n) F) a.1 b.1), ?_⟩
  apply Units.ext
  change fromBlocks 1 _ 0 1 = (g : Matrix (Fin n) (Fin n) F).submatrix (coarseEquiv blk j)
    (coarseEquiv blk j)
  ext a b
  rcases a with ⟨p, hp⟩ | ⟨p, hp⟩ <;> rcases b with ⟨q, hq⟩ | ⟨q, hq⟩
  · simp only [fromBlocks_apply₁₁, Matrix.submatrix_apply, coarseEquiv,
      Equiv.sumCompl_apply_inl]
    rw [hg p q (fun h => h.2 hq)]
    by_cases hpq : p = q
    · subst hpq; simp
    · rw [Matrix.one_apply_ne hpq, Matrix.one_apply_ne (fun h => hpq (congrArg Subtype.val h))]
  · rfl
  · simp only [fromBlocks_apply₂₁, Matrix.zero_apply, Matrix.submatrix_apply, coarseEquiv,
      Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr]
    rw [hg p q (fun h => hp h.1), Matrix.one_apply_ne (fun h => hp (by rw [h]; exact hq))]
  · simp only [fromBlocks_apply₂₂, Matrix.submatrix_apply, coarseEquiv,
      Equiv.sumCompl_apply_inr]
    rw [hg p q (fun h => hp h.1)]
    by_cases hpq : p = q
    · subst hpq; simp
    · rw [Matrix.one_apply_ne hpq, Matrix.one_apply_ne (fun h => hpq (congrArg Subtype.val h))]

/-- A permutation carrying the first `card Late` coordinates onto the late ones. -/
theorem exists_perm_late (blk : Fin n → ℕ) (j : ℕ) :
    ∃ σ : Equiv.Perm (Fin n), ∀ x : Fin n,
      (j ≤ blk (σ x) ↔ (x : ℕ) < Fintype.card (Late blk j)) := by
  classical
  set b := Fintype.card (Late blk j) with hb
  have hbn : b ≤ n := by
    rw [hb]
    simpa using Fintype.card_subtype_le (fun p : Fin n => j ≤ blk p)
  have hcardE : Fintype.card (Early blk j) = n - b := by
    rw [hb, Fintype.card_subtype_compl, Fintype.card_fin]
  let eL : Late blk j ≃ Fin b := Fintype.equivFin _
  let eE : Early blk j ≃ Fin (n - b) := Fintype.equivFinOfCardEq hcardE
  let cs : Fin b ⊕ Fin (n - b) ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))
  let σ : Equiv.Perm (Fin n) :=
    cs.symm.trans ((eL.symm.sumCongr eE.symm).trans (coarseEquiv blk j))
  refine ⟨σ, fun x => ?_⟩
  by_cases hx : (x : ℕ) < b
  · have hcs : cs.symm x = Sum.inl ⟨x, hx⟩ := by
      rw [Equiv.symm_apply_eq]
      ext
      simp [cs]
    have : σ x = (eL.symm ⟨x, hx⟩).val := by
      simp only [σ, Equiv.trans_apply, hcs, Equiv.sumCongr_apply, Sum.map_inl, coarseEquiv,
        Equiv.sumCompl_apply_inl]
    rw [this]
    exact ⟨fun _ => hx, fun _ => (eL.symm ⟨x, hx⟩).property⟩
  · have hx' : (x : ℕ) - b < n - b := by omega
    have hcs : cs.symm x = Sum.inr ⟨(x : ℕ) - b, hx'⟩ := by
      rw [Equiv.symm_apply_eq]
      ext
      simp only [cs, Equiv.trans_apply, finSumFinEquiv_apply_right, finCongr_apply, Fin.val_cast,
        Fin.val_natAdd]
      omega
    have : σ x = (eE.symm ⟨(x : ℕ) - b, hx'⟩).val := by
      simp only [σ, Equiv.trans_apply, hcs, Equiv.sumCongr_apply, Sum.map_inr, coarseEquiv,
        Equiv.sumCompl_apply_inr]
    rw [this]
    exact ⟨fun h => absurd h (eE.symm ⟨(x : ℕ) - b, hx'⟩).property, fun h => absurd h hx⟩

/-- **The conjugated two-block unipotent radical lies in the coarse corner.** -/
theorem conjugateUnipotent_le_coarseN {b : ℕ} (hb0 : 0 < b) (hbn : b < n)
    {σ : Equiv.Perm (Fin n)} (hσ : ∀ x : Fin n, (j ≤ blk (σ x) ↔ (x : ℕ) < b)) :
    (twoBlock n b hb0 hbn).conjugateUnipotent (permutation n F σ) ≤ coarseN F blk j := by
  rintro _ ⟨u, hu, rfl⟩
  apply mem_coarseN_of_entries
  intro p q hpq
  change (permutation n F σ * u * (permutation n F σ)⁻¹) p q = _
  rw [permutation_conjugate_entry]
  have e1 : σ (σ⁻¹ p) = p := σ.apply_symm_apply p
  have e2 : σ (σ⁻¹ q) = q := σ.apply_symm_apply q
  have hp := hσ (σ⁻¹ p)
  have hq := hσ (σ⁻¹ q)
  rw [e1] at hp
  rw [e2] at hq
  have h' : (σ⁻¹ q : ℕ) < b ∨ b ≤ (σ⁻¹ p : ℕ) := by
    by_contra hc
    rw [not_or, not_lt, not_le] at hc
    exact hpq ⟨hp.mpr hc.2, fun h => absurd (hq.mp h) (by omega)⟩
  rw [isBlockUnipotent_of_mem_cutShape hb0 hbn hu (σ⁻¹ p) (σ⁻¹ q) h']
  by_cases hpq' : p = q
  · subst hpq'; simp
  · rw [ite_eq_right (fun h => hpq' (σ⁻¹.injective h)), Matrix.one_apply_ne hpq']

end Langlands.BushnellKutzko.SplitTypeJacquet
