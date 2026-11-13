import Langlands.GroupScheme.Quaternionic.AntihermitianWittBasis

/-!
# Witt block decompositions of trace-valued antihermitian forms

Let `σ` be an involution of the first kind of a division algebra `D` over a field `K`, and
`H ∈ M_n(D)` an invertible trace-valued `σ`-antihermitian Gram matrix of Witt index `r`.
This module strengthens `exists_wittBasis`: there are an invertible `P`, an identification
`ε : n ≃ (Fin r ⊕ Fin r) ⊕ Fin d` of the rows, and a trace-valued antihermitian
`H_U ∈ M_d(D)` such that `P H ᵗP^σ` is exactly the Witt block matrix
`[[0, 1, 0], [-1, 0, 0], [0, 0, H_U]]` (`wittGram`) after relabelling the rows and columns by
`ε` (`exists_wittBlockBasis`). The rows of `P` are a hyperbolic family `x₁, …, x_r`,
`y₁, …, y_r` followed by a basis of its orthogonal complement, as in the proof of
`exists_wittBasis`.
-/

noncomputable section

universe u v

open Matrix

namespace Langlands.GroupScheme.AntihermitianSplitRank

open Quaternionic Quaternionic.FirstKindInvolution

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  (σ : FirstKindInvolution K D) {n : Type} [Fintype n] [DecidableEq n]

/-- The Witt block Gram matrix `[[0, 1, 0], [-1, 0, 0], [0, 0, H_U]]` on
`(Fin r ⊕ Fin r) ⊕ Fin d`. -/
def wittGram {r d : ℕ} (HU : Matrix (Fin d) (Fin d) D) :
    Matrix ((Fin r ⊕ Fin r) ⊕ Fin d) ((Fin r ⊕ Fin r) ⊕ Fin d) D :=
  Matrix.fromBlocks (Matrix.fromBlocks 0 1 (-1) 0) 0 0 HU

section WittBlock

variable [LinearOrder n]

variable {σ} in
/-- **Witt block bases.** For an invertible trace-valued antihermitian `H` of Witt index `r`
there are `d`, a relabelling `ε : n ≃ (Fin r ⊕ Fin r) ⊕ Fin d`, an invertible `P` and a
trace-valued antihermitian `H_U ∈ M_d(D)` with `(P H ᵗP^σ)_{ij} = wittGram H_U (ε i) (ε j)`. -/
theorem exists_wittBlockBasis {H : Matrix n n D} (hH : σ.IsAntihermitian H) (hu : IsUnit H) :
    ∃ (d : ℕ) (ε : n ≃ (Fin (σ.wittIndex H) ⊕ Fin (σ.wittIndex H)) ⊕ Fin d)
      (P : Matrix n n D) (HU : Matrix (Fin d) (Fin d) D),
      IsUnit P ∧ σ.IsAntihermitian HU ∧
        ∀ i j, (P * H * σ.matrix n P) i j = wittGram HU (ε i) (ε j) := by
  classical
  set r := σ.wittIndex H
  obtain ⟨x, y, hxx, hyy, hxy⟩ := exists_hyperbolic_family hH hu
  have hyx := sesqForm_swap_ite hH hxy
  -- the orthogonal complement of the hyperbolic family
  let χ : (n → D) →ₗ[D] (Fin r ⊕ Fin r → D) :=
    { toFun := fun v => Sum.elim (fun k => σ.sesqForm H v (x k)) (fun k => σ.sesqForm H v (y k))
      map_add' := fun v v' => by
        funext s
        rcases s with k | k <;> simp [σ.sesqForm_add_left]
      map_smul' := fun a v => by
        funext s
        rcases s with k | k <;> simp [σ.sesqForm_smul_left] }
  let U := LinearMap.ker χ
  have hU : ∀ z ∈ U, (∀ k, σ.sesqForm H z (x k) = 0) ∧ ∀ k, σ.sesqForm H z (y k) = 0 := by
    intro z hz
    have h := LinearMap.mem_ker.1 hz
    exact ⟨fun k => by simpa [χ] using congrFun h (Sum.inl k),
      fun k => by simpa [χ] using congrFun h (Sum.inr k)⟩
  have hdim : Fintype.card n ≤ r + r + Module.finrank D U := by
    have h := LinearMap.finrank_range_add_finrank_ker χ
    change _ + Module.finrank D U = _ at h
    have hr : Module.finrank D (LinearMap.range χ) ≤ r + r := by
      calc Module.finrank D (LinearMap.range χ) ≤ Module.finrank D (Fin r ⊕ Fin r → D) :=
            Submodule.finrank_le _
        _ = r + r := by simp
    rw [Module.finrank_fintype_fun_eq_card] at h
    omega
  set d := Module.finrank D U
  let bU := Module.finBasis D U
  have hUx : ∀ j k, σ.sesqForm H (bU j : n → D) (x k) = 0 := fun j k =>
    (hU _ (bU j).2).1 k
  have hUy : ∀ j k, σ.sesqForm H (bU j : n → D) (y k) = 0 := fun j k =>
    (hU _ (bU j).2).2 k
  have hxU : ∀ j k, σ.sesqForm H (x k) (bU j : n → D) = 0 := fun j k => by
    rw [IsAntihermitian.sesqForm_swap σ hH, hUx, FirstKindInvolution.map_zero, neg_zero]
  have hyU : ∀ j k, σ.sesqForm H (y k) (bU j : n → D) = 0 := fun j k => by
    rw [IsAntihermitian.sesqForm_swap σ hH, hUy, FirstKindInvolution.map_zero, neg_zero]
  -- the family `x, y, basis of U`
  let p : (Fin r ⊕ Fin r) ⊕ Fin d → n → D := Sum.elim (Sum.elim x y) fun j => (bU j : n → D)
  have hp : LinearIndependent D p := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hx0 : ∀ l, g (Sum.inl (Sum.inl l)) = 0 := by
      intro l
      have h := congrArg (fun v => σ.sesqForm H v (y l)) hg
      simp only [sesqForm_sum_left] at h
      simp only [σ.sesqForm_smul_left, Fintype.sum_sum_type, p,
        Sum.elim_inl, Sum.elim_inr, hxy, hyy, hUy, mul_zero, Finset.sum_const_zero, add_zero,
        mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
        σ.sesqForm_zero_left] at h
      exact h
    have hy0 : ∀ l, g (Sum.inl (Sum.inr l)) = 0 := by
      intro l
      have h := congrArg (fun v => σ.sesqForm H v (x l)) hg
      simp only [sesqForm_sum_left] at h
      simp only [σ.sesqForm_smul_left, Fintype.sum_sum_type, p,
        Sum.elim_inl, Sum.elim_inr, hxx, hyx, hUx, mul_zero, Finset.sum_const_zero, zero_add,
        add_zero, mul_neg, mul_ite, mul_one, Finset.sum_neg_distrib, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true, σ.sesqForm_zero_left, neg_eq_zero] at h
      exact h
    have hU0 : ∀ j, g (Sum.inr j) = 0 := by
      have h : ∑ j, g (Sum.inr j) • bU j = 0 := by
        apply Subtype.ext
        simp only [Fintype.sum_sum_type, p, Sum.elim_inl, Sum.elim_inr, hx0, hy0, zero_smul,
          Finset.sum_const_zero, zero_add] at hg
        simpa using hg
      exact (Fintype.linearIndependent_iff.1 bU.linearIndependent) _ h
    rintro ((l | l) | j)
    · exact hx0 l
    · exact hy0 l
    · exact hU0 j
  have hcard : Fintype.card ((Fin r ⊕ Fin r) ⊕ Fin d) = Fintype.card n := by
    have h := hp.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card] at h
    simp only [Fintype.card_sum, Fintype.card_fin] at h ⊢
    omega
  let e : n ≃ (Fin r ⊕ Fin r) ⊕ Fin d := Fintype.equivOfCardEq hcard.symm
  let P : Matrix n n D := Matrix.of fun i => p (e i)
  -- `P` is invertible
  have hProws : LinearIndependent D fun i => p (e i) := hp.comp e e.injective
  let V : (n → D) →ₗ[D] (n → D) :=
    { toFun := fun v => v ᵥ* P
      map_add' := fun v v' => Matrix.add_vecMul P v v'
      map_smul' := fun a v => Matrix.smul_vecMul a v P }
  have hVsum : ∀ v, v ᵥ* P = ∑ i, v i • p (e i) := by
    intro v
    funext j
    simp [Matrix.vecMul, dotProduct, P, Finset.sum_apply]
  have hVinj : Function.Injective V := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h : ∑ i, v i • p (e i) = 0 := by
      rw [← hVsum]
      exact hv
    funext i
    exact (Fintype.linearIndependent_iff.1 hProws) v h i
  have hVsurj := LinearMap.injective_iff_surjective.1 hVinj
  choose q hq using fun i : n => hVsurj (Pi.single i 1)
  let Q : Matrix n n D := Matrix.of q
  have hQP : Q * P = 1 := by
    ext i j
    have h := congrFun (hq i) j
    change (q i ᵥ* P) j = (Pi.single i (1 : D) : n → D) j at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Q, Matrix.of_apply]
    rw [Matrix.vecMul, dotProduct] at h
    rw [h, Pi.single_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  have hP : IsUnit P := ⟨⟨P, Q, mul_eq_one_symm hQP, hQP⟩, rfl⟩
  refine ⟨d, e, P, Matrix.of fun a b => σ.sesqForm H (bU a : n → D) (bU b), hP, ?_, ?_⟩
  · refine ⟨?_, fun a => sesqForm_self_mem_alternatingSubspace hH _⟩
    ext a b
    simp only [matrix_apply, Matrix.of_apply, Matrix.neg_apply]
    rw [IsAntihermitian.sesqForm_swap σ hH, FirstKindInvolution.map_neg,
      FirstKindInvolution.apply_apply]
  · intro i j
    rw [mul_mul_matrix_apply]
    change σ.sesqForm H (p (e i)) (p (e j)) = _
    generalize e i = s
    generalize e j = t
    rcases s with ((k | k) | a) <;> rcases t with ((l | l) | b) <;>
      simp only [p, wittGram, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply, Matrix.one_apply, Matrix.neg_apply, Matrix.of_apply, hxx, hyy, hxy,
        hyx, hxU, hyU, hUx, hUy]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rfl

end WittBlock

end Langlands.GroupScheme.AntihermitianSplitRank
