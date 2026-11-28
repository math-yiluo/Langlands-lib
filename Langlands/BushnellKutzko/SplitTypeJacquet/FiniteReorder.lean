import Langlands.Representation.FiniteGeneralLinear.HarishChandraSeries

/-! # Reordering the blocks of a finite cuspidal datum -/

noncomputable section

open Module Representation

namespace Langlands.BushnellKutzko.SplitTypeJacquet

open Langlands.FiniteGeneralLinear Langlands.GeneralLinear Langlands.FiniteRep

variable {k : Type*} [Field k] {n : ℕ}

/-- The block shape with the blocks of `B` listed in the order `σ`. -/
def permuteShape (B : BlockShape n) (σ : Equiv.Perm (Fin B.length)) : BlockShape n where
  length := B.length
  size i := B.size (σ i)
  positive i := B.positive (σ i)
  sum_eq := by rw [Equiv.sum_comp σ B.size]; exact B.sum_eq

/-- The cuspidal datum with the blocks of `E` listed in the order `σ`. -/
def permuteDatum (E : HarishChandraDatum n k)
    (σ : Equiv.Perm (Fin E.shape.length)) : HarishChandraDatum n k where
  shape := permuteShape E.shape σ
  label i := E.label (σ i)

@[simp] theorem permuteDatum_blockLabel (E : HarishChandraDatum n k)
    (σ : Equiv.Perm (Fin E.shape.length)) (i : Fin (permuteDatum E σ).shape.length) :
    (permuteDatum E σ).blockLabel i = E.blockLabel (σ i) := rfl

theorem permuteDatum_labels (E : HarishChandraDatum n k)
    (σ : Equiv.Perm (Fin E.shape.length)) : (permuteDatum E σ).labels = E.labels := by
  change (Finset.univ.val.map (fun i => E.blockLabel (σ i)) :
    Multiset (PositiveCuspidalLabel k)) = Finset.univ.val.map E.blockLabel
  calc
    _ = (Finset.univ.val.map σ).map E.blockLabel := by
      simp only [Multiset.map_map, Function.comp_def]
    _ = _ := congrArg (Multiset.map E.blockLabel)
      (congrArg Finset.val (Finset.map_univ_equiv σ))

/-- A cuspidal datum with two different block labels can be reordered so that some cut `j`,
`0 < j` and `j` less than the number of blocks, separates the labels: no block before the cut has
the same label as a block after it. The witness puts first the blocks carrying the label of one
chosen block, so in it the first `j` blocks share one label; the statement exports only the
separation across the cut. -/
theorem exists_permute_separated (E : HarishChandraDatum n k)
    (h : ∃ i i', E.blockLabel i ≠ E.blockLabel i') :
    ∃ σ : Equiv.Perm (Fin E.shape.length), ∃ j : ℕ, 0 < j ∧ j < E.shape.length ∧
      ∀ i i' : Fin E.shape.length, (i : ℕ) < j → j ≤ (i' : ℕ) →
        E.blockLabel (σ i) ≠ E.blockLabel (σ i') := by
  classical
  obtain ⟨i₀, i₁, hne⟩ := h
  let ℓ := E.blockLabel i₀
  let S : Finset (Fin E.shape.length) := Finset.univ.filter (fun i => E.blockLabel i = ℓ)
  let j := S.card
  have hj₀ : 0 < j := Finset.card_pos.mpr ⟨i₀, by simp [S, ℓ]⟩
  have hjlt : j < E.shape.length := by
    have hlt : S.card < (Finset.univ : Finset (Fin E.shape.length)).card :=
      Finset.card_lt_card ⟨Finset.subset_univ _, fun hsub => hne (by
        have := hsub (Finset.mem_univ i₁)
        simp only [S, Finset.mem_filter] at this
        exact this.2.symm)⟩
    simpa using hlt
  -- an equivalence `Fin len ≃ Fin len` sending the first `j` indices onto `S`
  let eS : Fin j ≃ {i // i ∈ S} := (S.equivFin).symm
  let eT : Fin (E.shape.length - j) ≃ {i // i ∉ S} :=
    (finCongr (by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe])).trans
      (Fintype.equivFin {i // i ∉ S}).symm
  let e₀ : Fin j ⊕ Fin (E.shape.length - j) ≃ Fin E.shape.length :=
    (eS.sumCongr eT).trans (Equiv.sumCompl (fun i => i ∈ S))
  let σ : Equiv.Perm (Fin E.shape.length) :=
    (finCongr (by omega : E.shape.length = j + (E.shape.length - j))).trans
      (finSumFinEquiv.symm.trans e₀)
  have hσ : ∀ i : Fin E.shape.length, (σ i ∈ S ↔ (i : ℕ) < j) := by
    intro i
    by_cases hi : (i : ℕ) < j
    · have : finSumFinEquiv.symm (finCongr (by omega : E.shape.length = j +
          (E.shape.length - j)) i) = Sum.inl ⟨i, hi⟩ := by
        rw [Equiv.symm_apply_eq]
        ext
        simp
      simp only [σ, e₀, Equiv.trans_apply, this, Equiv.sumCongr_apply, Sum.map_inl,
        Equiv.sumCompl_apply_inl]
      exact ⟨fun _ => hi, fun _ => (eS ⟨i, hi⟩).property⟩
    · have hi' : (i : ℕ) - j < E.shape.length - j := by omega
      have : finSumFinEquiv.symm (finCongr (by omega : E.shape.length = j +
          (E.shape.length - j)) i) = Sum.inr ⟨(i : ℕ) - j, hi'⟩ := by
        rw [Equiv.symm_apply_eq]
        ext
        simp only [finSumFinEquiv_apply_right, Fin.val_natAdd, finCongr_apply, Fin.val_cast]
        omega
      simp only [σ, e₀, Equiv.trans_apply, this, Equiv.sumCongr_apply, Sum.map_inr,
        Equiv.sumCompl_apply_inr]
      exact ⟨fun h' => absurd h' (eT ⟨(i : ℕ) - j, hi'⟩).property, fun h' => absurd h' hi⟩
  refine ⟨σ, j, hj₀, hjlt, fun i i' hi hi' => ?_⟩
  have h₁ : σ i ∈ S := (hσ i).mpr hi
  have h₂ : σ i' ∉ S := fun h' => absurd ((hσ i').mp h') (by omega)
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
  rw [h₁]
  exact fun h' => h₂ h'.symm

variable [Finite k]

/-- Two cuspidal data with the same label multiset have parabolic intertwiners into the same
finite-dimensional representations of `GL_n(k)`, by Frobenius reciprocity and the equality of
the constituent multiplicities of their Harish–Chandra inductions. -/
theorem finrank_parabolicHom_eq_of_labels_eq (E E' : HarishChandraDatum n k)
    (h : E.labels = E'.labels) (X : FDRep ℂ (GeneralLinear n k)) :
    finrank ℂ (IntertwiningMap (pullbackRep (E.shape.leviProjection k) E.leviRep).ρ
        (X.ρ.comp (E.shape.parabolic k).subtype)) =
      finrank ℂ (IntertwiningMap (pullbackRep (E'.shape.leviProjection k) E'.leviRep).ρ
        (X.ρ.comp (E'.shape.parabolic k).subtype)) := by
  classical
  let := Fintype.ofFinite (GeneralLinear n k)
  let := Fintype.ofFinite (IrreducibleClass (GeneralLinear n k))
  rw [← finrank_intertwiningMap_induceRep_left, ← finrank_intertwiningMap_induceRep_left]
  change finrank ℂ (IntertwiningMap E.induced.ρ X.ρ) = finrank ℂ (IntertwiningMap E'.induced.ρ X.ρ)
  rw [finrank_intertwiningMap_eq_sum_constituentMultiplicity,
    finrank_intertwiningMap_eq_sum_constituentMultiplicity]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [constituentMultiplicity_eq_of_labels_eq E E' h a]

end Langlands.BushnellKutzko.SplitTypeJacquet
