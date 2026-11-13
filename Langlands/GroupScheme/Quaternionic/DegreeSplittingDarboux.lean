import Langlands.GroupScheme.Quaternionic.DegreeSplittingMatrix
import Langlands.GroupScheme.Quaternionic.AntihermitianWittBlock
import Langlands.GroupScheme.SymplecticMatrix.Darboux

/-!
# Darboux matrices adapted to a Witt block decomposition

Let `D` be a central division algebra of degree `δ` over `K` with an involution of the first
kind `σ` whose symmetric elements have dimension `δ (δ + 1) / 2`, and let
`e : L ⊗[K] D ≃ₐ[L] M_δ(L)` be a matrix chart over a field extension `L`. Suppose that the Gram
matrix `H' ∈ M_m(D)` is, after relabelling its rows and columns by
`ε : Fin m ≃ (Fin r ⊕ Fin r) ⊕ Fin d`, the Witt block matrix `[[0, 1, 0], [-1, 0, 0], [0, 0, H_U]]`
(`AntihermitianSplitRank.wittGram`). This module constructs rectangular matrices `P`, `P'` over
`L` with `P P' = 1`, `P' P = 1` and `P C Pᵀ = J` for the split Gram matrix `C = splitGram e σ H'`
on `Fin m × Fin δ`, where `J` is the standard alternating matrix on `Fin N ⊕ Fin N` and
`m δ = 2 N` (`exists_wittDarboux`). Moreover `P` is homogeneous for the weights of the Witt torus:
row `inl a` (resp. `inr a`) of `P` has weight `blockWeight δ r a` (resp. its negative), the
indicator of the block `k δ ≤ a < (k + 1) δ`, and column `(i, c)` has weight `wittWeight (ε i)`,
which is `e_k`, `-e_k` or `0` on the three kinds of Witt coordinates. Also `r δ ≤ N`.

The construction is explicit on the hyperbolic part: the coordinate `(x_k, a)` is sent to the
row `inl` of index `a + δ k`, and the coordinates `(y_k, ·)` are combined with the matrix
`-S⁻¹`, `S` the symmetric involution matrix of the chart. On the anisotropic part `H_U` it uses
the Darboux normal form `SymplecticMatrix.exists_mul_mul_transpose_eq_J` of the alternating
matrix `splitGram e σ H_U`.
-/

noncomputable section

universe u

open Matrix Module
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic

namespace DegreeSplitting

open AntihermitianSplitRank (wittGram)

section Apply

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  {L : Type u} [Field L] [Algebra K L]
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (e : L ⊗[K] D ≃ₐ[L] Matrix ι ι L) (σ : FirstKindInvolution K D)

/-- Entries of the split Gram matrix: the `(i, j)` block is `e (1 ⊗ H_{ij}) S`. -/
theorem splitGram_apply {n : Type} [Fintype n] [DecidableEq n] (G : Matrix n n D) (i j : n)
    (a b : ι) :
    splitGram e σ G (i, a) (j, b) =
      (e (1 ⊗ₜ[K] G i j) * (involutionMatrix e σ : Matrix ι ι L)) a b := by
  rw [splitGram, Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single j]
  · rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [matrixChartR_tmul_apply, blockInvolutionMatrix, Matrix.comp_apply, Matrix.diagonal_apply_eq,
      one_mul, Algebra.algebraMap_self, RingHom.id_apply]
  · intro j' _ hj'
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [blockInvolutionMatrix, Matrix.comp_apply, Matrix.diagonal_apply_ne _ hj', Matrix.zero_apply,
      mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

end Apply

/-! ### Weights -/

/-- The weights of the Witt torus on Witt block coordinates: `e_k` on `x_k`, `-e_k` on `y_k`
and `0` on the anisotropic part. -/
def wittWeight {r d : ℕ} : (Fin r ⊕ Fin r) ⊕ Fin d → Fin r → ℤ
  | Sum.inl (Sum.inl k) => Pi.single k 1
  | Sum.inl (Sum.inr k) => -Pi.single k 1
  | Sum.inr _ => 0

/-- The weight of the coordinate `a` of the diagonal torus of `Sp_{2N}`: the indicator of the
block `k δ ≤ a < (k + 1) δ` containing `a`. -/
def blockWeight (δ r : ℕ) {N : ℕ} (a : Fin N) : Fin r → ℤ :=
  fun k => if k.val * δ ≤ a.val ∧ a.val < (k.val + 1) * δ then 1 else 0

/-- The weights of the rows `Fin N ⊕ Fin N` of a Darboux matrix: `blockWeight` on `inl a` and
its negative on `inr a`. -/
def darbouxWeight (δ r : ℕ) {N : ℕ} : Fin N ⊕ Fin N → Fin r → ℤ :=
  Sum.elim (blockWeight δ r) fun a => -blockWeight δ r a

theorem block_iff {δ c k l : ℕ} (hc : c < δ) :
    (l * δ ≤ c + δ * k ∧ c + δ * k < (l + 1) * δ) ↔ l = k := by
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : l < k + 1 := by
      by_contra h
      have := Nat.mul_le_mul_right δ (Nat.le_of_not_lt h)
      nlinarith
    have h4 : k < l + 1 := by
      by_contra h
      have := Nat.mul_le_mul_right δ (Nat.le_of_not_lt h)
      nlinarith
    omega
  · rintro rfl
    constructor <;> nlinarith

theorem blockWeight_eq_single {δ r N : ℕ} (a : Fin N) (c : Fin δ) (k : Fin r)
    (ha : a.val = c.val + δ * k.val) : blockWeight δ r a = Pi.single k 1 := by
  funext l
  rw [blockWeight, ha, Pi.single_apply]
  by_cases hlk : l = k
  · subst hlk
    simp [(block_iff c.2).2 rfl]
  · have h : ¬ (l.val * δ ≤ c.val + δ * k.val ∧ c.val + δ * k.val < (l.val + 1) * δ) :=
      fun h => hlk (Fin.ext ((block_iff c.2).1 h))
    simp only [h, hlk, ↓reduceIte]

theorem blockWeight_eq_zero {δ r N : ℕ} (a : Fin N) (ha : r * δ ≤ a.val) :
    blockWeight δ r a = 0 := by
  funext l
  simp only [blockWeight, Pi.zero_apply, ite_eq_right_iff]
  rintro ⟨-, h2⟩
  have := Nat.mul_le_mul_right δ (show l.val + 1 ≤ r from l.2)
  omega

/-! ### The Darboux matrix -/

section Darboux

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  {L : Type u} [Field L] [Algebra K L] {δ : ℕ}
  (e : L ⊗[K] D ≃ₐ[L] Matrix (Fin δ) (Fin δ) L) (σ : FirstKindInvolution K D)

/-- **Witt-adapted Darboux matrices.** If `H'` is the Witt block matrix of `H_U` after the
relabelling `ε`, its split Gram matrix has a Darboux matrix `P` (with two-sided inverse `P'`)
which is homogeneous for the Witt weights and the block weights; moreover `r δ ≤ N`. -/
theorem exists_wittDarboux
    (hσ : finrank K σ.symmetricSubspace = δ * (δ + 1) / 2)
    {m r d : ℕ} (ε : Fin m ≃ (Fin r ⊕ Fin r) ⊕ Fin d) {H' : Matrix (Fin m) (Fin m) D}
    {HU : Matrix (Fin d) (Fin d) D} (hHU : σ.IsAntihermitian HU) (hu : IsUnit H')
    (hH' : ∀ i j, H' i j = wittGram HU (ε i) (ε j)) {N : ℕ} (hN : m * δ = 2 * N) :
    r * δ ≤ N ∧ ∃ (P : Matrix (Fin N ⊕ Fin N) (Fin m × Fin δ) L)
      (P' : Matrix (Fin m × Fin δ) (Fin N ⊕ Fin N) L),
      P * P' = 1 ∧ P' * P = 1 ∧ P * splitGram e σ H' * Pᵀ = J (Fin N) L ∧
      ∀ α β, P α β ≠ 0 → darbouxWeight δ r α = wittWeight (ε β.1) := by
  classical
  have hσ' : finrank K σ.symmetricSubspace =
      Fintype.card (Fin δ) * (Fintype.card (Fin δ) + 1) / 2 := by
    rwa [Fintype.card_fin]
  set S : Matrix (Fin δ) (Fin δ) L := (involutionMatrix e σ : Matrix (Fin δ) (Fin δ) L)
    with hSdef
  have hST : Sᵀ = S := involutionMatrix_transpose e σ hσ'
  set Sinv : Matrix (Fin δ) (Fin δ) L :=
    (((involutionMatrix e σ)⁻¹ : (Matrix (Fin δ) (Fin δ) L)ˣ) : Matrix (Fin δ) (Fin δ) L)
  have hSinvS : Sinv * S = 1 := Units.inv_mul _
  -- the reindexing of the columns
  let colE : Fin m × Fin δ ≃ ((Fin δ × Fin r) ⊕ (Fin δ × Fin r)) ⊕ (Fin d × Fin δ) :=
    (Equiv.prodCongr ε (Equiv.refl (Fin δ))).trans ((Equiv.sumProdDistrib _ _ _).trans
      (Equiv.sumCongr ((Equiv.sumProdDistrib _ _ _).trans
        (Equiv.sumCongr (Equiv.prodComm _ _) (Equiv.prodComm _ _))) (Equiv.refl _)))
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix (Fin δ × Fin r) (Fin δ × Fin r) L,
      Y = blockDiagonal fun _ => S := ⟨_, rfl⟩
  have he1 : e (1 ⊗ₜ[K] (1 : D)) = 1 := by rw [← Algebra.TensorProduct.one_def, map_one]
  have hem1 : e (1 ⊗ₜ[K] (-1 : D)) = -1 := by rw [TensorProduct.tmul_neg, map_neg, he1]
  let CU := splitGram e σ HU
  let C0 : Matrix (((Fin δ × Fin r) ⊕ (Fin δ × Fin r)) ⊕ (Fin d × Fin δ))
      (((Fin δ × Fin r) ⊕ (Fin δ × Fin r)) ⊕ (Fin d × Fin δ)) L :=
    fromBlocks (fromBlocks 0 Y (-Y) 0) 0 0 CU
  have hC : splitGram e σ H' = C0.submatrix colE colE := by
    ext ⟨i, a⟩ ⟨j, b⟩
    rw [splitGram_apply, hH', Matrix.submatrix_apply]
    simp only [colE, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]
    generalize ε i = s
    generalize ε j = t
    rcases s with ((k | k) | v) <;> rcases t with ((l | l) | w) <;>
      simp [wittGram, C0, hY, CU, splitGram_apply, blockDiagonal_apply, Matrix.one_apply,
        apply_ite, ite_mul, he1, hem1] <;>
      by_cases hkl : k = l <;> simp [hkl, hSdef]
  -- the anisotropic part
  have hdetC : (splitGram e σ H').det ≠ 0 := det_splitGram_ne_zero e σ hu
  have hdetCU : CU.det ≠ 0 := by
    rw [hC, det_submatrix_equiv_self, det_fromBlocks_zero₂₁] at hdetC
    exact right_ne_zero_of_mul hdetC
  obtain ⟨k0, PU, PU', hPU1, hPU2, hPUJ⟩ :=
    SymplecticMatrix.exists_mul_mul_transpose_eq_J CU (transpose_splitGram e σ hσ' hHU)
      (splitGram_diag e σ hσ' hHU) hdetCU
  have hk0 : 2 * k0 = d * δ := by
    have h1 : Fintype.card (Fin k0 ⊕ Fin k0) ≤ Fintype.card (Fin d × Fin δ) := by
      calc Fintype.card (Fin k0 ⊕ Fin k0)
            = (1 : Matrix (Fin k0 ⊕ Fin k0) (Fin k0 ⊕ Fin k0) L).rank := (rank_one).symm
        _ = (PU * PU').rank := by rw [hPU1]
        _ ≤ PU.rank := rank_mul_le_left _ _
        _ ≤ _ := rank_le_card_width _
    have h2 : Fintype.card (Fin d × Fin δ) ≤ Fintype.card (Fin k0 ⊕ Fin k0) := by
      calc Fintype.card (Fin d × Fin δ)
            = (1 : Matrix (Fin d × Fin δ) (Fin d × Fin δ) L).rank := (rank_one).symm
        _ = (PU' * PU).rank := by rw [hPU2]
        _ ≤ PU'.rank := rank_mul_le_left _ _
        _ ≤ _ := rank_le_card_width _
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at h1 h2
    omega
  have hm : m = r + r + d := by
    simpa using Fintype.card_congr ε
  have hN' : N = r * δ + k0 := by
    have h : m * δ = 2 * (r * δ) + d * δ := by rw [hm]; ring
    generalize r * δ = A at h ⊢
    generalize d * δ = B at h hk0
    omega
  refine ⟨by omega, ?_⟩
  -- the Darboux matrix in block form
  let Q : Matrix (Fin δ) (Fin δ) L := -Sinv
  obtain ⟨Q2, hQ2⟩ : ∃ Q2 : Matrix (Fin δ × Fin r) (Fin δ × Fin r) L,
      Q2 = blockDiagonal fun _ => Q := ⟨_, rfl⟩
  let P0 : Matrix (((Fin δ × Fin r) ⊕ (Fin δ × Fin r)) ⊕ (Fin k0 ⊕ Fin k0))
      (((Fin δ × Fin r) ⊕ (Fin δ × Fin r)) ⊕ (Fin d × Fin δ)) L :=
    fromBlocks (fromBlocks 1 0 0 Q2) 0 0 PU
  have hQS : Q * S = -1 := by
    simp only [Q, Matrix.neg_mul, hSinvS]
  have hSQ : S * Qᵀ = -1 := by
    rw [← hST, ← Matrix.transpose_mul, hQS, Matrix.transpose_neg, Matrix.transpose_one]
  have hneg1 : (fun _ : Fin r => (-1 : Matrix (Fin δ) (Fin δ) L)) = -1 := rfl
  have hYQ : Y * Q2ᵀ = -1 := by
    rw [hY, hQ2, blockDiagonal_transpose, ← blockDiagonal_mul]
    simp only [hSQ]
    rw [hneg1, blockDiagonal_neg, blockDiagonal_one]
  have hQY : Q2 * Y = -1 := by
    rw [hY, hQ2, ← blockDiagonal_mul]
    simp only [hQS]
    rw [hneg1, blockDiagonal_neg, blockDiagonal_one]
  have hP0 : P0 * C0 * P0ᵀ = fromBlocks (J (Fin δ × Fin r) L) 0 0 (J (Fin k0) L) := by
    simp only [P0, C0, fromBlocks_transpose, fromBlocks_multiply, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add, Matrix.transpose_zero, Matrix.transpose_one,
      Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, hPUJ, hYQ, hQY, neg_neg,
      neg_zero]
    rfl
  -- the reindexing of the rows
  let eA : (Fin δ × Fin r) ⊕ Fin k0 ≃ Fin N :=
    (Equiv.sumCongr ((Equiv.prodComm _ _).trans finProdFinEquiv) (Equiv.refl _)).trans
      (finSumFinEquiv.trans (finCongr hN'.symm))
  have heA_inl : ∀ c k, (eA (Sum.inl (c, k))).val = c.val + δ * k.val := by
    intro c k
    simp [eA, finProdFinEquiv]
  have heA_inr : ∀ b, (eA (Sum.inr b)).val = r * δ + b.val := by
    intro b
    simp [eA]
  let rowE : Fin N ⊕ Fin N ≃ ((Fin δ × Fin r) ⊕ (Fin δ × Fin r)) ⊕ (Fin k0 ⊕ Fin k0) :=
    (Equiv.sumCongr eA.symm eA.symm).trans (Equiv.sumSumSumComm _ _ _ _)
  have hJ : (fromBlocks (J (Fin δ × Fin r) L) 0 0 (J (Fin k0) L)).submatrix rowE rowE =
      J (Fin N) L := by
    ext α β
    rcases α with a | a <;> rcases β with b | b <;>
      obtain ⟨a', rfl⟩ := eA.surjective a <;> obtain ⟨b', rfl⟩ := eA.surjective b <;>
      rcases a' with a' | a' <;> rcases b' with b' | b' <;>
      simp [rowE, J, Matrix.one_apply]
  let P : Matrix (Fin N ⊕ Fin N) (Fin m × Fin δ) L := P0.submatrix rowE colE
  have hPJ : P * splitGram e σ H' * Pᵀ = J (Fin N) L := by
    rw [hC, Matrix.transpose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hP0, hJ]
  let P' : Matrix (Fin m × Fin δ) (Fin N ⊕ Fin N) L := splitGram e σ H' * Pᵀ * (-J (Fin N) L)
  have hPP' : P * P' = 1 := by
    simp only [P']
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPJ, Matrix.mul_neg, J_squared, neg_neg]
  have hcard : Fintype.card (Fin N ⊕ Fin N) = Fintype.card (Fin m × Fin δ) := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, hN]
    omega
  have eqv : Fin N ⊕ Fin N ≃ Fin m × Fin δ := Fintype.equivOfCardEq hcard
  refine ⟨P, P', hPP', (mul_eq_one_comm_of_equiv eqv).1 hPP', hPJ, ?_⟩
  -- homogeneity
  let V0 : ((Fin δ × Fin r) ⊕ (Fin δ × Fin r)) ⊕ (Fin k0 ⊕ Fin k0) → Fin r → ℤ :=
    Sum.elim (Sum.elim (fun p => Pi.single p.2 1) fun p => -Pi.single p.2 1) 0
  let W0 : ((Fin δ × Fin r) ⊕ (Fin δ × Fin r)) ⊕ (Fin d × Fin δ) → Fin r → ℤ :=
    Sum.elim (Sum.elim (fun p => Pi.single p.2 1) fun p => -Pi.single p.2 1) 0
  have hP0w : ∀ x y, P0 x y ≠ 0 → V0 x = W0 y := by
    rintro ((⟨c, k⟩ | ⟨c, k⟩) | x) ((⟨c', k'⟩ | ⟨c', k'⟩) | y) h <;>
      simp [P0, hQ2, V0, W0, blockDiagonal_apply, Matrix.one_apply] at h ⊢
    · rw [h.2]
    · rw [h.1]
  have hV : ∀ α, darbouxWeight δ r α = V0 (rowE α) := by
    rintro (a | a) <;> obtain ⟨a', rfl⟩ := eA.surjective a <;> rcases a' with ⟨c, k⟩ | b
    · simp only [darbouxWeight, Sum.elim_inl, rowE, Equiv.trans_apply, Equiv.sumCongr_apply,
        Sum.map_inl, Equiv.symm_apply_apply, Equiv.sumSumSumComm, V0]
      rw [blockWeight_eq_single _ c k (heA_inl c k)]
      rfl
    · simp only [darbouxWeight, Sum.elim_inl, rowE, Equiv.trans_apply, Equiv.sumCongr_apply,
        Sum.map_inl, Equiv.symm_apply_apply, Equiv.sumSumSumComm, V0]
      rw [blockWeight_eq_zero _ (by rw [heA_inr]; omega)]
      rfl
    · simp only [darbouxWeight, Sum.elim_inr, rowE, Equiv.trans_apply, Equiv.sumCongr_apply,
        Sum.map_inr, Equiv.symm_apply_apply, Equiv.sumSumSumComm, V0]
      rw [blockWeight_eq_single _ c k (heA_inl c k)]
      rfl
    · simp only [darbouxWeight, Sum.elim_inr, rowE, Equiv.trans_apply, Equiv.sumCongr_apply,
        Sum.map_inr, Equiv.symm_apply_apply, Equiv.sumSumSumComm, V0]
      rw [blockWeight_eq_zero _ (by rw [heA_inr]; omega), neg_zero]
      rfl
  have hW : ∀ β : Fin m × Fin δ, wittWeight (ε β.1) = W0 (colE β) := by
    rintro ⟨i, c⟩
    simp only [colE, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]
    generalize ε i = s
    rcases s with ((k | k) | v) <;> rfl
  intro α β h
  rw [hV, hW]
  exact hP0w _ _ h

end Darboux

end DegreeSplitting

end Langlands.GroupScheme.Quaternionic
