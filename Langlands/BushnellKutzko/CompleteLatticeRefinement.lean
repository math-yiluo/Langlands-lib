import Langlands.BushnellKutzko.CompleteLatticeChain
import Langlands.BushnellKutzko.FundamentalStratumPowerCondition
import Langlands.BushnellKutzko.LatticeChainGradedMatrices
import Langlands.BushnellKutzko.LatticeChainShifts
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Prod.Lex.Basic

/-! # Refinement of a lattice chain to a complete chain -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.LatticeChain

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {π : 𝒪[F]} (hπ : Irreducible π)
  {V : Type uV} [AddCommGroup V] [Module F V] (L : LatticeChain 𝒪[F] F V)

private theorem exists_sortingPerm {d : ℕ} (ν : Fin d → ℤ) :
    ∃ e : Fin d ≃ Fin d, Monotone (ν ∘ e) := by
  classical
  let k : Fin d ↪ ℤ ×ₗ Fin d :=
    ⟨fun j => toLex (ν j, j), fun _ _ h => congrArg (fun x => (ofLex x).2) h⟩
  let s := Finset.univ.map k
  have hs : s.card = d := by simp [s]
  let e : Fin d ≃ s := Equiv.ofBijective (fun j => ⟨k j, by simp [s]⟩)
    ⟨fun _ _ h => k.injective (congrArg Subtype.val h), fun p => by
      obtain ⟨j, -, h⟩ := Finset.mem_map.mp p.2
      exact ⟨j, Subtype.ext h⟩⟩
  let o := s.orderIsoOfFin hs
  refine ⟨o.toEquiv.trans e.symm, fun i j hij => ?_⟩
  have h (i : Fin d) : k (e.symm (o i)) = (o i).val :=
    congrArg Subtype.val (e.apply_symm_apply (o i))
  have h' : k (e.symm (o i)) ≤ k (e.symm (o j)) := by
    rw [h, h]
    exact o.monotone hij
  exact (Prod.Lex.le_iff'.mp h').1

private theorem exists_basis_sorted :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) F V), L.Splits b ∧
      (∀ i, 0 ≤ L.index hπ (b i) ∧ L.index hπ (b i) < L.period) ∧
      Monotone (fun i => L.index hπ (b i)) := by
  obtain ⟨d, b, hb, hn⟩ := L.exists_basis_splits_normalized hπ
  obtain ⟨e, he⟩ := exists_sortingPerm fun i => L.index hπ (b i)
  refine ⟨d, b.reindex e.symm, ?_, ?_, ?_⟩
  · intro c j hj t
    have hs : ∑ i, c (e.symm i) • b i ∈ L.lattice j := by
      rw [← e.symm.sum_comp (fun i => c i • b.reindex e.symm i)] at hj
      simpa only [Module.Basis.reindex_apply, Equiv.symm_apply_apply] using hj
    simpa only [Equiv.symm_apply_apply, Equiv.symm_symm, Module.Basis.reindex_apply] using
      hb (fun i => c (e.symm i)) j hs (e t)
  · intro i
    simpa only [Module.Basis.reindex_apply, Equiv.symm_symm] using hn (e i)
  · intro i j hij
    simpa only [Module.Basis.reindex_apply, Equiv.symm_symm, Function.comp_apply] using he hij

private theorem mem_lattice_of_splitting_iff {d : ℕ} (b : Module.Basis (Fin d) F V)
    (hb : L.Splits b) (i : ℤ) (v : V) :
    v ∈ L.lattice i ↔ ∀ j, b.equivFun v j ≠ 0 →
      i ≤ L.index hπ (b j) + L.period * ordOf hπ (b.equivFun v j) := by
  have hv : ∑ j, b.equivFun v j • b j = v := by
    simp only [Module.Basis.equivFun_apply, b.sum_repr]
  constructor
  · intro h j hj
    have h' := hb (b.equivFun v) i (hv.symm ▸ h) j
    rwa [L.mem_iff_le_index hπ (smul_ne_zero hj (b.ne_zero j)),
      L.index_smul hπ hj (b.ne_zero j)] at h'
  · intro h
    rw [← hv]
    apply Submodule.sum_mem
    intro j _
    by_cases hj : b.equivFun v j = 0
    · simp [hj]
    rw [L.mem_iff_le_index hπ (smul_ne_zero hj (b.ne_zero j)),
      L.index_smul hπ hj (b.ne_zero j)]
    exact h j hj

private theorem exists_cut {d : ℕ} {ν : Fin d → ℤ} (hν : Monotone ν) (a : ℤ) :
    ∃ t : ℕ, t ≤ d ∧ ∀ j : Fin d, t ≤ j.val ↔ a ≤ ν j := by
  classical
  let s := Finset.univ.filter (fun j => a ≤ ν j)
  by_cases hs : s.Nonempty
  · let j₀ := s.min' hs
    have hj₀ : a ≤ ν j₀ := (Finset.mem_filter.mp (s.min'_mem hs)).2
    refine ⟨j₀.val, j₀.isLt.le, fun j => ⟨fun h => hj₀.trans (hν h), fun h => ?_⟩⟩
    exact s.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  · refine ⟨d, le_rfl, fun j => ⟨fun h => (j.isLt.not_ge h).elim, fun h => ?_⟩⟩
    exact (hs ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩).elim

private theorem gradeLe_iff {D q m t ν : ℤ} (hD : 0 < D)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ D) (hν₀ : 0 ≤ ν) (hν₁ : ν < D) :
    D * q + t ≤ ν + D * m ↔ q < m ∨ q = m ∧ t ≤ ν := by
  rcases lt_trichotomy m q with h | rfl | h
  · have hh := mul_le_mul_of_nonneg_left (show m ≤ q - 1 by omega) hD.le
    rw [mul_sub, mul_one] at hh
    omega
  · omega
  · have hh := mul_le_mul_of_nonneg_left (show q + 1 ≤ m by omega) hD.le
    rw [mul_add, mul_one] at hh
    omega

include hπ in
/-- A lattice chain can be refined by the complete chain of an ordered
splitting basis. All its lattices occur in the refinement. -/
theorem exists_complete_refinement :
    ∃ M : LatticeChain 𝒪[F] F V,
      M.period = Module.finrank F V ∧ M.lattice 0 = L.lattice 0 ∧
      ∀ i : ℤ, ∃ j : ℤ, M.lattice j = L.lattice i := by
  obtain ⟨d, b, hb, hn, hm⟩ := L.exists_basis_sorted hπ
  let _ := L.nontrivialSpace
  have hd : 0 < d := Fintype.card_fin d ▸ Fintype.card_pos_iff.mpr (b.index_nonempty)
  let M := (completeChain hπ hd).linearEquivMap b.equivFun.symm
  have hM (i : ℤ) (v : V) : v ∈ M.lattice i ↔
      ∀ j, b.equivFun v j ≠ 0 → i ≤ (j : ℕ) + (d : ℤ) * ordOf hπ (b.equivFun v j) := by
    rw [mem_linearEquivMap, mem_completeChain]
    rfl
  have hper : M.period = Module.finrank F V := by
    rw [period_linearEquivMap, period_completeChain, Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hD : (0 : ℤ) < d := by exact_mod_cast hd
  have hP : (0 : ℤ) < L.period := by exact_mod_cast L.period_pos
  have aux (q a : ℤ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ L.period)
      (t : ℕ) (ht : t ≤ d) (hc : ∀ j : Fin d, t ≤ j.val ↔ a ≤ L.index hπ (b j)) :
      M.lattice ((d : ℤ) * q + t) = L.lattice ((L.period : ℤ) * q + a) := by
    ext v
    rw [hM, L.mem_lattice_of_splitting_iff hπ b hb]
    refine forall_congr' fun j => imp_congr_right fun _ => ?_
    rw [gradeLe_iff hD (by exact_mod_cast Nat.zero_le t) (by exact_mod_cast ht)
      (by exact_mod_cast Nat.zero_le j.val) (by exact_mod_cast j.isLt),
      gradeLe_iff hP ha₀ ha₁ (hn j).1 (hn j).2]
    have he : (t : ℤ) ≤ (j.val : ℤ) ↔ a ≤ L.index hπ (b j) := by exact_mod_cast hc j
    rw [he]
  refine ⟨M, hper, ?_, fun i => ?_⟩
  · simpa using aux 0 0 le_rfl hP.le 0 (Nat.zero_le _) (fun j => by simp [(hn j).1])
  · let q := i / (L.period : ℤ)
    let a := i % (L.period : ℤ)
    obtain ⟨t, ht, hc⟩ := exists_cut hm a
    refine ⟨(d : ℤ) * q + t, ?_⟩
    rw [aux q a (Int.emod_nonneg _ hP.ne') (Int.emod_lt_of_pos _ hP).le t ht hc]
    congr 1
    exact Int.mul_ediv_add_emod i L.period

end Langlands.BushnellKutzko.LatticeChain
