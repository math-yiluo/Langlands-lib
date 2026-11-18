import Langlands.LinearAlgebra.FiniteCartanLocalStructure
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-! # The underlying graph of a finite Cartan matrix -/

universe u v

open Matrix Finset SimpleGraph

namespace Langlands.LinearAlgebra.FiniteCartanMatrix

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
  {M : Matrix ι ι ℤ}

/-- The unoriented graph of nonzero off-diagonal Cartan pairs. -/
def diagram (M : Matrix ι ι ℤ) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ M i j ≠ 0 ∧ M j i ≠ 0
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel (diagram M).Adj := fun _ _ => inferInstanceAs
  (Decidable (_ ≠ _ ∧ _ ≠ (0 : ℤ) ∧ _ ≠ (0 : ℤ)))

theorem diagram_adj_iff (hM : M.IsFiniteCartan) (i j : ι) :
    (diagram M).Adj i j ↔ i ≠ j ∧ M i j < 0 := by
  constructor
  · rintro ⟨hne, h, _⟩
    exact ⟨hne, lt_of_le_of_ne (hM.offDiag_nonpos _ _ hne) h⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, h.ne, mt (hM.zero_comm _ _).mpr h.ne⟩

theorem matrix_le_graphCartan (hM : M.IsFiniteCartan)
    (H : SimpleGraph ι) [DecidableRel H.Adj] (hH : H ≤ diagram M) :
    ∀ i j, M i j ≤
      (Matrix.diagonal (fun _ : ι => (2 : ℤ)) - H.adjMatrix ℤ) i j := by
  intro i j
  by_cases hij : i = j
  · subst j
    simp [hM.diag]
  · by_cases hadj : H.Adj i j
    · have hneg := ((diagram_adj_iff hM i j).mp (hH hadj)).2
      simp [Matrix.diagonal, hij, SimpleGraph.adjMatrix_apply, hadj]
      omega
    · simpa [Matrix.diagonal, hij, SimpleGraph.adjMatrix_apply, hadj] using
        hM.offDiag_nonpos i j hij

theorem exists_degree_le_one [Nonempty ι] (hM : M.IsFiniteCartan)
    (H : SimpleGraph ι) [DecidableRel H.Adj] (hH : H ≤ diagram M) :
    ∃ i, H.degree i ≤ 1 := by
  have hx0 : (fun _ : ι => (1 : ℤ)) ≠ 0 := by
    intro h
    have := congr_fun h (Classical.arbitrary ι)
    norm_num at this
  obtain ⟨i, _, hi⟩ := exists_positive_mulVec hM (fun _ => 1) (fun _ => by omega) hx0
  have hle : (M *ᵥ (fun _ => 1)) i ≤
      ((Matrix.diagonal (fun _ => (2 : ℤ)) - H.adjMatrix ℤ) *ᵥ
        (fun _ => 1)) i := by
    simp only [Matrix.mulVec, dotProduct, mul_one]
    exact Finset.sum_le_sum (fun j _ => matrix_le_graphCartan hM H hH i j)
  have heq : ((Matrix.diagonal (fun _ => (2 : ℤ)) - H.adjMatrix ℤ) *ᵥ
        (fun _ => 1)) i = 2 - (H.degree i : ℤ) := by
    rw [Matrix.sub_mulVec]
    simp only [Pi.sub_apply, Matrix.mulVec_diagonal, mul_one]
    change 2 - (H.adjMatrix ℤ *ᵥ Function.const ι 1) i = _
    simp
  rw [heq] at hle
  exact ⟨i, by omega⟩

theorem diagram_isAcyclic (hM : M.IsFiniteCartan) :
    (diagram M).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_free_cycleGraph]
  intro n hn hcopy
  obtain ⟨f⟩ := hcopy
  have hsub := finiteCartan_submatrix hM f.injective
  have hle : SimpleGraph.cycleGraph n ≤ diagram (M.submatrix f f) := by
    intro i j hij
    have hf := f.toHom.map_adj hij
    exact ⟨fun h => hij.ne h, hf.2.1, hf.2.2⟩
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨i, hi⟩ := exists_degree_le_one hsub (SimpleGraph.cycleGraph n) hle
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have hdeg : (SimpleGraph.cycleGraph (k + 3)).degree i = 2 :=
    SimpleGraph.cycleGraph_degree_three_le
  omega

omit [DecidableEq ι] in
theorem indecomposable_exists_crossing (hI : M.IsIndecomposable)
    (p : ι → Prop) (a b : ι) (ha : p a) (hb : ¬p b) :
    ∃ i j, ¬p i ∧ p j ∧ M i j ≠ 0 := by
  classical
  by_contra h
  push Not at h
  let ep := (Fintype.equivFin {i // p i}).symm
  let en := (Fintype.equivFin {i // ¬p i}).symm
  let e := (Equiv.sumCongr ep en).trans (Equiv.sumCompl p)
  let A : Matrix (Fin (Fintype.card {i // p i}))
      (Fin (Fintype.card {i // p i})) ℤ :=
    fun i j => M (ep i) (ep j)
  let B : Matrix (Fin (Fintype.card {i // p i}))
      (Fin (Fintype.card {i // ¬p i})) ℤ :=
    fun i j => M (ep i) (en j)
  let D : Matrix (Fin (Fintype.card {i // ¬p i}))
      (Fin (Fintype.card {i // ¬p i})) ℤ :=
    fun i j => M (en i) (en j)
  have heq : M = (Matrix.fromBlocks A B 0 D).reindex e e := by
    ext i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, e.symm_apply_apply]
    cases i with
    | inl i =>
      cases j <;> rfl
    | inr i =>
      cases j with
      | inl j => exact h _ _ (en i).property (ep j).property
      | inr j => rfl
  have hc := hI _ _ A B D e heq
  have hp : 0 < Fintype.card {i // p i} :=
    Fintype.card_pos_iff.mpr ⟨⟨a, ha⟩⟩
  have hn : 0 < Fintype.card {i // ¬p i} :=
    Fintype.card_pos_iff.mpr ⟨⟨b, hb⟩⟩
  omega

theorem diagram_connected [Nonempty ι] (hM : M.IsFiniteCartan)
    (hI : M.IsIndecomposable) : (diagram M).Connected := by
  classical
  refine { preconnected := ?_ }
  intro u v
  by_contra h
  obtain ⟨i, j, hi, hj, hij⟩ := indecomposable_exists_crossing hI
    (fun w => (diagram M).Reachable u w) u v SimpleGraph.Reachable.rfl h
  have hne : i ≠ j := by
    intro heq
    subst j
    exact hi hj
  have hadj : (diagram M).Adj j i :=
    ⟨hne.symm, mt (hM.zero_comm j i).mp hij, hij⟩
  exact hi (hj.trans hadj.reachable)

theorem diagram_isTree [Nonempty ι] (hM : M.IsFiniteCartan)
    (hI : M.IsIndecomposable) : (diagram M).IsTree :=
  ⟨diagram_connected hM hI, diagram_isAcyclic hM⟩

theorem diagram_degree_le_three (hM : M.IsFiniteCartan) (i : ι) :
    (diagram M).degree i ≤ 3 := by
  have hsubset : (diagram M).neighborFinset i ⊆ Finset.univ.erase i := by
    intro j hj
    have hadj := (SimpleGraph.mem_neighborFinset _ _ _).mp hj
    exact Finset.mem_erase.mpr ⟨hadj.ne.symm, Finset.mem_univ j⟩
  have hle : ((diagram M).degree i : ℤ) ≤
      ∑ j ∈ Finset.univ.erase i, M i j * M j i := by
    calc
      _ = ∑ _j ∈ (diagram M).neighborFinset i, (1 : ℤ) := by
        simp
      _ ≤ ∑ j ∈ (diagram M).neighborFinset i, M i j * M j i := by
        apply Finset.sum_le_sum
        intro j hj
        have hadj := (SimpleGraph.mem_neighborFinset _ _ _).mp hj
        have hnz := hadj.2.1
        rcases ordered_entries hM i j hadj.ne with h | h | h | h | h | h <;>
          simp_all
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro j hj _
        have hji := (Finset.mem_erase.mp hj).1
        exact mul_nonneg_of_nonpos_of_nonpos
          (hM.offDiag_nonpos _ _ hji.symm) (hM.offDiag_nonpos _ _ hji))
  have hbound := row_edgeProduct_sum_le_three hM i
  omega

end Langlands.LinearAlgebra.FiniteCartanMatrix
