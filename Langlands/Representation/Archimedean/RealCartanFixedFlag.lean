import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.Linarith

/-! # Fixed block flags of normal real matrices -/

open Matrix

namespace Langlands.Archimedean.RealCartanFixedFlag

set_option autoImplicit false

variable {ι α β : Type*} [Fintype ι]

/-- A normal real matrix that is upper triangular by blocks is block diagonal.
At each cut of the ordered row blocks, compare the sum of the squared row norms
against the sum of the squared column norms on the same indices. -/
theorem eq_zero_of_block_ne_of_normal [LinearOrder β] {A : Matrix ι ι ℝ} {b : ι → β}
    (hA : A * Aᵀ = Aᵀ * A) (hbelow : A.BlockTriangular b)
    {i j : ι} (hij : b i ≠ b j) : A i j = 0 := by
  classical
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · let S : Finset ι := Finset.univ.filter fun k => b k ≤ b i
    let T : Finset ι := Finset.univ.filter fun k => ¬ b k ≤ b i
    have hST (k : ι) :
        (∑ l ∈ S, A k l ^ 2) + (∑ l ∈ T, A k l ^ 2) = ∑ l, A k l ^ 2 :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    have hTS (k : ι) :
        (∑ l ∈ S, A l k ^ 2) + (∑ l ∈ T, A l k ^ 2) = ∑ l, A l k ^ 2 :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    have hi : i ∈ S := by simp [S]
    have hj : j ∈ T := by simpa [T] using hlt
    have hz (k : ι) (hk : k ∈ S) (l : ι) (hl : l ∈ T) : A l k = 0 := by
      have hk' : b k ≤ b i := (Finset.mem_filter.mp hk).2
      have hl' : b i < b l := lt_of_not_ge (Finset.mem_filter.mp hl).2
      exact hbelow (hk'.trans_lt hl')
    have hrows (k : ι) (hk : k ∈ S) :
        (∑ l ∈ S, A k l ^ 2) + (∑ l ∈ T, A k l ^ 2) = ∑ l ∈ S, A l k ^ 2 := by
      have he := congrArg (fun M : Matrix ι ι ℝ => M k k) hA
      simp only [Matrix.mul_apply, Matrix.transpose_apply, ← pow_two] at he
      rw [hST, he, ← hTS]
      simpa using (Finset.sum_eq_zero fun l hl => by rw [hz k hk l hl, zero_pow (by decide)])
    have htot := Finset.sum_congr rfl (fun k hk => hrows k hk)
    rw [Finset.sum_add_distrib, Finset.sum_comm (s := S) (t := S)] at htot
    have hzero : ∑ k ∈ S, ∑ l ∈ T, A k l ^ 2 = 0 := by linarith
    have hi0 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
      Finset.sum_nonneg fun l _ => sq_nonneg (A k l))).mp hzero i hi
    have hj0 := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => sq_nonneg (A i l))).mp hi0 j hj
    exact (mul_eq_zero.mp (by simpa [pow_two] using hj0)).elim id id
  · exact hbelow hgt

variable [DecidableEq ι]

private theorem conj_mul (Q A B : Matrix ι ι ℝ) (hQ : Qᵀ * Q = 1) :
    (Q * A * Qᵀ) * (Q * B * Qᵀ) = Q * (A * B) * Qᵀ := by
  calc
    _ = Q * A * (Qᵀ * Q) * B * Qᵀ := by simp only [mul_assoc]
    _ = _ := by rw [hQ, mul_one, mul_assoc Q A B]

private theorem conj_cancel (Q A : Matrix ι ι ℝ) (hQ : Qᵀ * Q = 1) :
    Qᵀ * (Q * A * Qᵀ) * Q = A := by
  calc
    _ = (Qᵀ * Q) * A * (Qᵀ * Q) := by simp only [mul_assoc]
    _ = _ := by simp [hQ]

private theorem eq_zero_of_commute_diagonal {P : Matrix ι ι ℝ} {d : ι → ℝ}
    (h : P * diagonal d = diagonal d * P) {i j : ι} (hij : d i ≠ d j) :
    P i j = 0 := by
  have he := congrArg (fun A : Matrix ι ι ℝ => A i j) h
  simp only [mul_diagonal, diagonal_mul] at he
  exact (mul_eq_zero.mp (show P i j * (d i - d j) = 0 by linarith)).resolve_right
    (sub_ne_zero.mpr hij)

private theorem mul_apply_of_support_pair {M N : Matrix ι ι ℝ} {i j l : ι}
    (hij : i ≠ j) (h : ∀ k, k ≠ i → k ≠ j → M i k * N k l = 0) :
    (M * N) i l = M i i * N i l + M i j * N j l := by
  classical
  rw [Matrix.mul_apply, ← Finset.sum_subset (Finset.subset_univ {i, j})]
  · simp [hij]
  · intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    exact h k hk.1 hk.2

private theorem symmetric_commutant_of_cartan {a : ι → α} {d : α → ℝ}
    {C P : Matrix ι ι ℝ}
    (hsize : ∀ ⦃i j k⦄, i ≠ j → a i = a j → a k = a i → k = i ∨ k = j)
    (hCzero : ∀ ⦃i j⦄, a i ≠ a j → C i j = 0)
    (hCskew : ∀ ⦃i j⦄, i ≠ j → a i = a j → C i j = - C j i)
    (hCpair : ∀ ⦃i j⦄, i ≠ j → a i = a j → C i j ≠ 0)
    (hGram : C * Cᵀ = diagonal (d ∘ a)) (hd : Function.Injective d)
    (hPsymm : Pᵀ = P) (hPC : P * C = C * P) :
    P = diagonal (fun i => P i i) ∧ (∀ i j, a i = a j → P i i = P j j) := by
  have hPCt : P * Cᵀ = Cᵀ * P := by
    simpa only [transpose_mul, hPsymm] using
      (congrArg Matrix.transpose hPC).symm
  have hPGram : P * diagonal (d ∘ a) = diagonal (d ∘ a) * P := by
    rw [← hGram, ← mul_assoc, hPC, mul_assoc, hPCt, ← mul_assoc]
  have hPzero {i j : ι} (hij : a i ≠ a j) : P i j = 0 :=
    eq_zero_of_commute_diagonal hPGram (fun h => hij (hd h))
  have hdiag : P = diagonal (fun i => P i i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    rw [diagonal_apply_ne _ hij]
    by_cases ha : a i = a j
    · have hskew := hCskew hij ha
      have hpairs (k : ι) (hki : k ≠ i) (hkj : k ≠ j) : a k ≠ a i := fun hki' =>
        (hsize hij ha hki').elim hki hkj
      have he := congrArg (fun A : Matrix ι ι ℝ => A i i) hPC
      rw [mul_apply_of_support_pair hij (fun k hki hkj =>
          by rw [hPzero (Ne.symm (hpairs k hki hkj)), zero_mul]),
        mul_apply_of_support_pair hij (fun k hki hkj =>
          by rw [hCzero (Ne.symm (hpairs k hki hkj)), zero_mul])] at he
      have hsymm : P j i = P i j := congrArg (fun A : Matrix ι ι ℝ => A i j) hPsymm
      rw [hsymm, hskew] at he
      have hprod : P i j * C j i = 0 := by linarith
      exact (mul_eq_zero.mp hprod).resolve_right (hCpair (Ne.symm hij) ha.symm)
    · exact hPzero ha
  refine ⟨hdiag, fun i j ha => ?_⟩
  by_cases hij : i = j
  · subst j
    rfl
  have he : diagonal (fun k => P k k) * C = C * diagonal (fun k => P k k) := by
    rw [← hdiag]
    exact hPC
  have hentry := congrArg (fun A : Matrix ι ι ℝ => A i j) he
  simpa only [diagonal_mul, mul_diagonal, mul_comm (P i i),
    mul_right_inj' (hCpair hij ha)] using hentry

private theorem exists_perm_support {Q : Matrix ι ι ℝ} (hQ : Qᵀ * Q = 1) :
    ∃ π : Equiv.Perm ι, ∀ i, Q (π i) i ≠ 0 := by
  classical
  have hdet : Q.det ≠ 0 := by
    intro hzero
    have h := congrArg Matrix.det hQ
    simp [Matrix.det_mul, Matrix.det_transpose, hzero] at h
  by_contra! h
  apply hdet
  rw [Matrix.det_apply]
  refine Finset.sum_eq_zero fun π _ => ?_
  obtain ⟨i, hi⟩ := h π
  rw [Finset.prod_eq_zero (f := fun j => Q (π j) j) (Finset.mem_univ i) hi, smul_zero]

/-- A fixed block flag for a normal Cartan matrix with one- or two-dimensional slots
has a matching of columns to rows that places each source slot wholly inside one
target block. All nonzero entries of a column belong to its matched block. -/
def RealCartanFixedFlagStatement (ι α β : Type*) [Fintype ι] [DecidableEq ι]
    [LinearOrder β] : Prop :=
  ∀ (a : ι → α) (b : ι → β) (d : α → ℝ) (C Q : Matrix ι ι ℝ),
    (∀ ⦃i j k⦄, i ≠ j → a i = a j → a k = a i → k = i ∨ k = j) →
    (∀ ⦃i j⦄, a i ≠ a j → C i j = 0) →
    (∀ ⦃i j⦄, i ≠ j → a i = a j → C i j = - C j i) →
    (∀ ⦃i j⦄, i ≠ j → a i = a j → C i j ≠ 0) →
    C * Cᵀ = diagonal (d ∘ a) → Function.Injective d → C * Cᵀ = Cᵀ * C →
    Qᵀ * Q = 1 → Q * Qᵀ = 1 → (Q * C * Qᵀ).BlockTriangular b →
    ∃ π : Equiv.Perm ι, (∀ i j, a i = a j → b (π i) = b (π j)) ∧
      ∀ u i, b u ≠ b (π i) → Q u i = 0

theorem exists_perm_of_fixedFlag [LinearOrder β] : RealCartanFixedFlagStatement ι α β := by
  classical
  intro a b d C Q hsize hCzero hCskew hCpair hGram hd hC hQt hQ htri
  let A := Q * C * Qᵀ
  have hAt : Aᵀ = Q * Cᵀ * Qᵀ := by simp [A, transpose_mul, mul_assoc]
  have hA : A * Aᵀ = Aᵀ * A := by
    rw [hAt, show A = Q * C * Qᵀ from rfl, conj_mul _ _ _ hQt, conj_mul _ _ _ hQt, hC]
  have hAzero {i j : ι} (hij : b i ≠ b j) : A i j = 0 :=
    eq_zero_of_block_ne_of_normal hA htri hij
  obtain ⟨π, hπ⟩ := exists_perm_support hQt
  have hlabel (v : β) :
      ∃ x : ι → ℝ, (∀ i j, a i = a j → x i = x j) ∧
        ∀ u i, Q u i ≠ 0 → x i = if b u = v then 1 else 0 := by
    let e : ι → ℝ := fun u => if b u = v then 1 else 0
    let E := diagonal e
    let P := Qᵀ * E * Q
    have hEA : E * A = A * E := by
      ext i j
      simp only [E, diagonal_mul, mul_diagonal]
      by_cases hij : b i = b j
      · simp [e, hij, mul_comm]
      · simp [hAzero hij]
    have hP : Pᵀ = P := by simp [P, E, transpose_mul, mul_assoc]
    have hPC : P * C = C * P := by
      have h := congrArg (fun M : Matrix ι ι ℝ => Qᵀ * M * Q) hEA
      change Qᵀ * (E * A) * Q = Qᵀ * (A * E) * Q at h
      have hm (X Y : Matrix ι ι ℝ) :
          Qᵀ * (X * Y) * Q = (Qᵀ * X * Q) * (Qᵀ * Y * Q) := by
        simpa only [transpose_transpose] using (conj_mul Qᵀ X Y (by simpa using hQ)).symm
      rw [hm E A, hm A E, show Qᵀ * A * Q = C from conj_cancel Q C hQt] at h
      exact h
    obtain ⟨hdiag, hconst⟩ :=
      symmetric_commutant_of_cartan hsize hCzero hCskew hCpair hGram hd hP hPC
    refine ⟨fun i => P i i, hconst, fun u i hu => ?_⟩
    have h := calc
      Q * diagonal (fun i => P i i) = Q * P := by rw [← hdiag]
      _ = (Q * Qᵀ) * E * Q := by simp only [P, mul_assoc]
      _ = E * Q := by rw [hQ, one_mul]
    have he := congrArg (fun M : Matrix ι ι ℝ => M u i) h
    simp only [E, mul_diagonal, diagonal_mul, mul_comm (e u), mul_right_inj' hu] at he
    exact he
  refine ⟨π, ?_, ?_⟩
  · intro i j ha
    obtain ⟨x, hx, hxentry⟩ := hlabel (b (π i))
    have hxi : x i = 1 := by simpa using hxentry (π i) i (hπ i)
    have hxj := hxentry (π j) j (hπ j)
    rw [← hx i j ha, hxi] at hxj
    by_contra h
    simp [Ne.symm h] at hxj
  · intro u i hne
    by_contra hu
    obtain ⟨x, _, hxentry⟩ := hlabel (b (π i))
    have hxi : x i = 1 := by simpa using hxentry (π i) i (hπ i)
    have hxu : x i = 0 := by simpa [hne] using hxentry u i hu
    exact one_ne_zero (hxi.symm.trans hxu)

end Langlands.Archimedean.RealCartanFixedFlag
