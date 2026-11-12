import Langlands.GroupScheme.Quaternionic.FormLemmas
import Langlands.GroupScheme.Quaternionic.StandardGenerationTwo
import Langlands.GroupScheme.Quaternionic.StandardGenerationThree

/-!
# Hyperbolic bases of antihermitian forms of Witt index one

Let `σ` be an involution of the first kind of a division algebra `D` and `H ∈ M_m(D)` a
nondegenerate trace-valued `σ`-antihermitian Gram matrix of Witt index `1`. For `m = 2` there
is an invertible `P` with `P H ᵗP^σ = !![0, 1; -1, 0]`, and for `m = 3` an invertible `P` and a
nonzero `c ∈ {a - σ a}` with `P H ᵗP^σ = !![0, 1, 0; -1, 0, 0; 0, 0, c]`. The rows of `P` are an
isotropic vector `e`, a vector `f` with `h(e, f) = 1` and `h(f, f) = 0`, and, for `m = 3`, a
nonzero vector `w` orthogonal to `e` and `f`.
-/

noncomputable section

open Matrix

universe u v w

namespace Langlands.GroupScheme.Quaternionic

namespace FirstKindInvolution

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  (σ : FirstKindInvolution K D) {n : Type w} [Fintype n] [DecidableEq n]

/-! ### Semilinearity of the form -/

section Sesquilinear

variable (H : Matrix n n D)

omit [DecidableEq n] in
/-- The form as a sum over the row vector `x H`. -/
theorem sesqForm_eq_sum_vecMul (x y : n → D) :
    σ.sesqForm H x y = ∑ j, (x ᵥ* H) j * σ (y j) := by
  simp only [sesqForm, Matrix.vecMul, dotProduct, Finset.sum_mul]
  exact Finset.sum_comm

/-- The entries of `P H ᵗP^σ` are the values of the form on the rows of `P`. -/
theorem mul_mul_matrix_apply (P : Matrix n n D) (i j : n) :
    (P * H * σ.matrix n P) i j = σ.sesqForm H (P i) (P j) := by
  simp only [Matrix.mul_apply, matrix_apply, sesqForm, Finset.sum_mul]
  exact Finset.sum_comm

end Sesquilinear

variable {σ}

/-- A trace-valued antihermitian matrix is `A - ᵗA^σ` for some `A`: take the strictly upper
part of `H` and diagonal entries `a i` with `H i i = a i - σ (a i)`. -/
theorem exists_eq_sub_matrix [LinearOrder n] {H : Matrix n n D} (hH : σ.IsAntihermitian H) :
    ∃ A : Matrix n n D, H = A - σ.matrix n A := by
  choose a ha using fun i => σ.mem_alternatingSubspace.1 (hH.2 i)
  have hH' : ∀ i j, σ (H j i) = -H i j := fun i j => by
    simpa using congrFun (congrFun hH.1 i) j
  refine ⟨Matrix.of fun i j => if i < j then H i j else if i = j then a i else 0, ?_⟩
  ext i j
  simp only [Matrix.sub_apply, matrix_apply, Matrix.of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.not_gt, h.ne']
  · simp [ha]
  · simp [h, h.not_gt, h.ne', hH']

/-- A trace-valued antihermitian form takes values `h(x, x) ∈ {a - σ a}`. -/
theorem sesqForm_self_mem_alternatingSubspace [LinearOrder n] {H : Matrix n n D}
    (hH : σ.IsAntihermitian H) (x : n → D) :
    σ.sesqForm H x x ∈ σ.alternatingSubspace := by
  obtain ⟨A, rfl⟩ := σ.exists_eq_sub_matrix hH
  have e : σ.sesqForm (A - σ.matrix n A) x x = σ.sesqForm A x x - σ (σ.sesqForm A x x) := by
    rw [σ.map_sesqForm_self]
    simp only [sesqForm, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [e]
  exact σ.sub_mem_alternatingSubspace _

/-- For invertible `H` and `x ≠ 0` there is `y` with `h(x, y) ≠ 0`. -/
theorem exists_sesqForm_ne_zero {H : Matrix n n D} (hu : IsUnit H) {x : n → D} (hx : x ≠ 0) :
    ∃ y, σ.sesqForm H x y ≠ 0 := by
  have hv : x ᵥ* H ≠ 0 := by
    intro h
    apply hx
    have e : x ᵥ* H ᵥ* ((hu.unit⁻¹ : (Matrix n n D)ˣ) : Matrix n n D) = x := by
      rw [Matrix.vecMul_vecMul, hu.mul_val_inv, Matrix.vecMul_one]
    rw [← e, h, Matrix.zero_vecMul]
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
  refine ⟨Pi.single j 1, ?_⟩
  rw [sesqForm_eq_sum_vecMul, Finset.sum_eq_single j
    (fun k _ hk => by simp [hk]) (by simp)]
  simpa using hj

/-! ### Witt index -/

omit [DecidableEq n] in
variable (σ) in
theorem bddAbove_isotropic_finrank (H : Matrix n n D) :
    BddAbove {r | ∃ W : Submodule D (n → D), σ.IsTotallyIsotropic H W ∧
      Module.finrank D W = r} := by
  refine ⟨Fintype.card n, ?_⟩
  rintro r ⟨W, -, rfl⟩
  calc Module.finrank D W ≤ Module.finrank D (n → D) := Submodule.finrank_le W
    _ = Fintype.card n := Module.finrank_fintype_fun_eq_card D

omit [DecidableEq n] in
/-- A form of Witt index one has a nonzero isotropic vector. -/
theorem exists_isotropic_of_wittIndex_eq_one {H : Matrix n n D} (h : σ.wittIndex H = 1) :
    ∃ e : n → D, e ≠ 0 ∧ σ.sesqForm H e e = 0 := by
  have hne : {r | ∃ W : Submodule D (n → D), σ.IsTotallyIsotropic H W ∧
      Module.finrank D W = r}.Nonempty :=
    ⟨0, ⊥, fun x hx y _ => by
      rw [(Submodule.mem_bot D).1 hx]
      simp [sesqForm], finrank_bot D (n → D)⟩
  have hmem := Nat.sSup_mem hne (σ.bddAbove_isotropic_finrank H)
  change σ.wittIndex H ∈ _ at hmem
  rw [h] at hmem
  obtain ⟨W, hW, hW1⟩ := hmem
  have hbot : W ≠ ⊥ := by
    rintro rfl
    simp at hW1
  obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  exact ⟨e, he0, hW e he e he⟩

/-! ### Hyperbolic pairs -/

/-- An isotropic vector `e ≠ 0` of a nondegenerate trace-valued antihermitian form has a
partner `f` with `h(e, f) = 1` and `h(f, f) = 0`. -/
theorem exists_hyperbolic_pair [LinearOrder n] {H : Matrix n n D} (hH : σ.IsAntihermitian H)
    (hu : IsUnit H) {e : n → D} (he : e ≠ 0) (hee : σ.sesqForm H e e = 0) :
    ∃ f, σ.sesqForm H e f = 1 ∧ σ.sesqForm H f f = 0 := by
  obtain ⟨y', hey⟩ : ∃ y', σ.sesqForm H e y' = 1 := by
    obtain ⟨y, hy⟩ := σ.exists_sesqForm_ne_zero hu he
    refine ⟨(σ (σ.sesqForm H e y))⁻¹ • y, ?_⟩
    rw [sesqForm_smul_right, map_inv, apply_apply]
    exact mul_inv_cancel₀ hy
  have hye : σ.sesqForm H y' e = -1 := by
    rw [IsAntihermitian.sesqForm_swap σ hH, hey, map_one]
  obtain ⟨t, ht⟩ := σ.mem_alternatingSubspace.1 (sesqForm_self_mem_alternatingSubspace hH y')
  refine ⟨y' + (-t) • e, ?_, ?_⟩
  · rw [sesqForm_add_right, sesqForm_smul_right, hee, zero_mul, add_zero, hey]
  · rw [sesqForm_add_left, sesqForm_add_right, sesqForm_add_right, sesqForm_smul_left,
      sesqForm_smul_right, sesqForm_smul_left, sesqForm_smul_right, hee, hey, hye, ← ht]
    simp

/-- If `P H ᵗP^σ` is invertible, so is `P`. -/
theorem isUnit_of_mul_mul_matrix_eq {P H G : Matrix n n D} (hG : IsUnit G)
    (h : P * H * σ.matrix n P = G) : IsUnit P := by
  refine IsUnit.of_mul_eq_one (H * σ.matrix n P * ((hG.unit⁻¹ : (Matrix n n D)ˣ) :
    Matrix n n D)) ?_
  rw [← mul_assoc, ← mul_assoc, h, hG.mul_val_inv]

/-! ### Standard forms -/

/-- **Rank two.** A nondegenerate trace-valued antihermitian form of rank `2` and Witt index
`1` has Gram matrix `!![0, 1; -1, 0]` in a suitable basis. -/
theorem exists_gramTwo {H : Matrix (Fin 2) (Fin 2) D} (hH : σ.IsAntihermitian H)
    (hu : IsUnit H) (hw : σ.wittIndex H = 1) :
    ∃ P : Matrix (Fin 2) (Fin 2) D, IsUnit P ∧ P * H * σ.matrix (Fin 2) P = gramTwo D := by
  obtain ⟨e, he, hee⟩ := exists_isotropic_of_wittIndex_eq_one hw
  obtain ⟨f, hef, hff⟩ := exists_hyperbolic_pair hH hu he hee
  have hfe : σ.sesqForm H f e = -1 := by
    rw [IsAntihermitian.sesqForm_swap σ hH, hef, map_one]
  have hG : Matrix.of ![e, f] * H * σ.matrix (Fin 2) (Matrix.of ![e, f]) = gramTwo D := by
    have hrow : ∀ i, (Matrix.of ![e, f] : Matrix (Fin 2) (Fin 2) D) i = ![e, f] i :=
      fun _ => rfl
    ext i j
    rw [mul_mul_matrix_apply, hrow, hrow]
    fin_cases i <;> fin_cases j <;> simp [gramTwo, hee, hef, hfe, hff]
  exact ⟨_, isUnit_of_mul_mul_matrix_eq isUnit_gramTwo hG, hG⟩

/-- **Rank three.** A nondegenerate trace-valued antihermitian form of rank `3` and Witt index
`1` has Gram matrix `!![0, 1, 0; -1, 0, 0; 0, 0, c]` in a suitable basis, with
`c ∈ {a - σ a}` nonzero. -/
theorem exists_gramThree {H : Matrix (Fin 3) (Fin 3) D} (hH : σ.IsAntihermitian H)
    (hu : IsUnit H) (hw : σ.wittIndex H = 1) :
    ∃ (P : Matrix (Fin 3) (Fin 3) D) (c : D), c ∈ σ.alternatingSubspace ∧ c ≠ 0 ∧
      IsUnit P ∧ P * H * σ.matrix (Fin 3) P = gramThree c := by
  obtain ⟨e, he, hee⟩ := exists_isotropic_of_wittIndex_eq_one hw
  obtain ⟨f, hef, hff⟩ := exists_hyperbolic_pair hH hu he hee
  have hfe : σ.sesqForm H f e = -1 := by
    rw [IsAntihermitian.sesqForm_swap σ hH, hef, map_one]
  obtain ⟨w, hw0, hwe, hwf⟩ : ∃ w : Fin 3 → D, w ≠ 0 ∧ σ.sesqForm H w e = 0 ∧
      σ.sesqForm H w f = 0 := by
    let φ : (Fin 3 → D) →ₗ[D] (Fin 2 → D) :=
      { toFun := fun x => ![σ.sesqForm H x e, σ.sesqForm H x f]
        map_add' := fun x y => by
          ext i
          fin_cases i <;> simp [sesqForm_add_left]
        map_smul' := fun a x => by
          ext i
          fin_cases i <;> simp [sesqForm_smul_left] }
    have h := LinearMap.finrank_range_add_finrank_ker φ
    have hr : Module.finrank D (LinearMap.range φ) ≤ 2 := by
      calc Module.finrank D (LinearMap.range φ) ≤ Module.finrank D (Fin 2 → D) :=
            Submodule.finrank_le _
        _ = 2 := Module.finrank_fin_fun D
    rw [Module.finrank_fin_fun] at h
    have hk : LinearMap.ker φ ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at h
      omega
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
    have hφ := LinearMap.mem_ker.1 hw
    exact ⟨w, hw0, by simpa [φ] using congrFun hφ 0, by simpa [φ] using congrFun hφ 1⟩
  have hew : σ.sesqForm H e w = 0 := by
    rw [IsAntihermitian.sesqForm_swap σ hH, hwe, map_zero, neg_zero]
  have hfw : σ.sesqForm H f w = 0 := by
    rw [IsAntihermitian.sesqForm_swap σ hH, hwf, map_zero, neg_zero]
  have hc0 : σ.sesqForm H w w ≠ 0 := by
    intro hc
    have hli : LinearIndependent D ![e, w] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h1 := congrArg (fun z => σ.sesqForm H z f) hst
      simp only [sesqForm_add_left, sesqForm_smul_left, hef, hwf, mul_one, mul_zero,
        add_zero] at h1
      have h0 : σ.sesqForm H 0 f = 0 := by simp [sesqForm]
      rw [h0] at h1
      subst h1
      rw [zero_smul, zero_add, smul_eq_zero] at hst
      exact ⟨rfl, hst.resolve_right hw0⟩
    have hW : σ.IsTotallyIsotropic H (Submodule.span D (Set.range ![e, w])) := by
      intro x hx y hy
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D).1 hx
      obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D).1 hy
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        sesqForm_add_left, sesqForm_add_right, sesqForm_smul_left, sesqForm_smul_right,
        hee, hew, hwe, hc]
      simp
    have h2 := finrank_le_wittIndex σ hW
    rw [finrank_span_eq_card hli, hw] at h2
    simp at h2
  have hG : Matrix.of ![e, f, w] * H * σ.matrix (Fin 3) (Matrix.of ![e, f, w]) =
      gramThree (σ.sesqForm H w w) := by
    have hrow : ∀ i, (Matrix.of ![e, f, w] : Matrix (Fin 3) (Fin 3) D) i = ![e, f, w] i :=
      fun _ => rfl
    ext i j
    rw [mul_mul_matrix_apply, hrow, hrow]
    fin_cases i <;> fin_cases j <;> simp [gramThree, hee, hef, hfe, hff, hew, hfw, hwe, hwf]
  exact ⟨_, _, sesqForm_self_mem_alternatingSubspace hH w, hc0,
    isUnit_of_mul_mul_matrix_eq (isUnit_gramThree hc0) hG, hG⟩

end FirstKindInvolution

end Langlands.GroupScheme.Quaternionic
