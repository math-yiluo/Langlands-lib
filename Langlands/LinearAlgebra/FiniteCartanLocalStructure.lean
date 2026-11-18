import Langlands.LinearAlgebra.FiniteCartanLocalStructureStatement
import Mathlib.Tactic

/-! # Local finite Cartan restrictions -/

universe u v

open Matrix Finset

namespace Langlands.LinearAlgebra.FiniteCartanMatrix

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
  {M : Matrix ι ι ℤ}

theorem finiteCartan_submatrix (hM : M.IsFiniteCartan)
    {κ : Type v} [Fintype κ] [DecidableEq κ]
    {f : κ → ι} (hf : Function.Injective f) :
    (M.submatrix f f).IsFiniteCartan := by
  obtain ⟨d, hd, hpos⟩ := hM.exists_posDef
  refine ⟨fun i => hM.diag (f i),
    fun i j hij => hM.offDiag_nonpos _ _ (fun h => hij (hf h)),
    fun i j => hM.zero_comm _ _, d ∘ f, fun i => hd (f i), ?_⟩
  convert hpos.submatrix hf using 1
  ext i j
  simp [Matrix.diagonal_mul, Function.comp_def]

theorem exists_positive_mulVec (hM : M.IsFiniteCartan)
    (x : ι → ℤ) (hx : ∀ i, 0 ≤ x i) (hx0 : x ≠ 0) :
    ∃ i, 0 < x i ∧ 0 < (M *ᵥ x) i := by
  obtain ⟨d, hd, hpos⟩ := hM.exists_posDef
  by_contra h
  push Not at h
  have hle : ∀ i, x i * (d i * (M *ᵥ x) i) ≤ 0 := by
    intro i
    by_cases hi : x i = 0
    · simp [hi]
    · have hxi : 0 < x i := lt_of_le_of_ne (hx i) (Ne.symm hi)
      exact mul_nonpos_of_nonneg_of_nonpos (hx i)
        (mul_nonpos_of_nonneg_of_nonpos (hd i).le (h i hxi))
  have hp := hpos.dotProduct_mulVec_pos hx0
  have hn : x ⬝ᵥ ((Matrix.diagonal d * M) *ᵥ x) ≤ 0 := by
    simpa only [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, dotProduct]
      using Finset.sum_nonpos (fun i (_ : i ∈ Finset.univ) => hle i)
  simpa only [star_trivial] using (not_lt_of_ge hn hp)

theorem edgeProduct_lt_four (hM : M.IsFiniteCartan) (i j : ι) (hij : i ≠ j) :
    M i j * M j i < 4 := by
  let f : Fin 2 → ι := ![i, j]
  have hf : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f]
  have hp := (finiteCartan_submatrix hM hf).det_pos
  rw [Matrix.det_fin_two] at hp
  change 0 < M i i * M j j - M i j * M j i at hp
  rw [hM.diag i, hM.diag j] at hp
  linarith

theorem ordered_entries (hM : M.IsFiniteCartan) (i j : ι) (hij : i ≠ j) :
    (M i j = 0 ∧ M j i = 0) ∨
    (M i j = -1 ∧ M j i = -1) ∨
    (M i j = -1 ∧ M j i = -2) ∨
    (M i j = -2 ∧ M j i = -1) ∨
    (M i j = -1 ∧ M j i = -3) ∨
    (M i j = -3 ∧ M j i = -1) := by
  have hab := hM.offDiag_nonpos i j hij
  have hba := hM.offDiag_nonpos j i hij.symm
  have hprod := edgeProduct_lt_four hM i j hij
  by_cases hzero : M i j = 0
  · exact Or.inl ⟨hzero, (hM.zero_comm i j).mp hzero⟩
  · have hzero' : M j i ≠ 0 := mt (hM.zero_comm i j).mpr hzero
    have hab' : M i j + 1 ≤ 0 := by omega
    have hba' : M j i + 1 ≤ 0 := by omega
    have hlow : -3 ≤ M i j := by
      nlinarith [mul_nonneg_of_nonpos_of_nonpos hab hba']
    have hlow' : -3 ≤ M j i := by
      nlinarith [mul_nonneg_of_nonpos_of_nonpos hba hab']
    interval_cases h1 : M i j <;> interval_cases h2 : M j i <;>
      simp_all

theorem row_edgeProduct_sum_le_three (hM : M.IsFiniteCartan) (i : ι) :
    ∑ j ∈ Finset.univ.erase i, M i j * M j i ≤ 3 := by
  let x : ι → ℤ := fun j => if j = i then 2 else -M j i
  have hxi : x i = 2 := by simp [x]
  have hx : ∀ j, 0 ≤ x j := by
    intro j
    by_cases hji : j = i
    · simp [x, hji]
    · simp only [x, ite_eq_right hji]
      exact neg_nonneg.mpr (hM.offDiag_nonpos _ _ hji)
  have hx0 : x ≠ 0 := by
    intro h
    have := congr_fun h i
    simp [hxi] at this
  have hcenter : (M *ᵥ x) i =
      4 - ∑ j ∈ Finset.univ.erase i, M i j * M j i := by
    simp only [Matrix.mulVec, dotProduct]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    have hs : (∑ j ∈ Finset.univ.erase i, M i j * x j) =
        -(∑ j ∈ Finset.univ.erase i, M i j * M j i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      simp [x, (Finset.mem_erase.mp hj).1]
    rw [hs, hxi, hM.diag i]
    ring
  have hother : ∀ k, k ≠ i → (M *ᵥ x) k ≤ 0 := by
    intro k hki
    simp only [Matrix.mulVec, dotProduct]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩)]
    have hs : (∑ j ∈ (Finset.univ.erase i).erase k, M k j * x j) ≤ 0 := by
      apply Finset.sum_nonpos
      intro j hj
      have hjk := (Finset.mem_erase.mp hj).1
      exact mul_nonpos_of_nonpos_of_nonneg
        (hM.offDiag_nonpos k j hjk.symm) (hx j)
    have hxk : x k = -M k i := by simp [x, hki]
    rw [hM.diag k, hxk, hxi]
    linarith
  obtain ⟨k, _, hk⟩ := exists_positive_mulVec hM x hx hx0
  by_cases hki : k = i
  · subst k
    rw [hcenter] at hk
    omega
  · exact (not_lt_of_ge (hother k hki) hk).elim

end Langlands.LinearAlgebra.FiniteCartanMatrix

namespace Langlands.LinearAlgebra

theorem finiteCartanLocalStructure : FiniteCartanLocalStructureStatement.{u, v} := by
  intro ι _ _ M hM
  exact ⟨fun _ _ _ _ hf => FiniteCartanMatrix.finiteCartan_submatrix hM hf,
    FiniteCartanMatrix.exists_positive_mulVec hM,
    FiniteCartanMatrix.ordered_entries hM,
    FiniteCartanMatrix.row_edgeProduct_sum_le_three hM⟩

end Langlands.LinearAlgebra
