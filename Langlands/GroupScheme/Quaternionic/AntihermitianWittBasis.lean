import Langlands.GroupScheme.Quaternionic.HyperbolicBasis
import Langlands.GroupScheme.Quaternionic.IsometryWeights
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Witt bases of trace-valued antihermitian forms

Let `σ` be an involution of the first kind of a division algebra `D` over a field `K`, and
`H ∈ M_n(D)` an invertible trace-valued `σ`-antihermitian Gram matrix of Witt index `r`.
This module produces vectors `x₁, …, x_r, y₁, …, y_r` with `h(x_k, x_l) = h(y_k, y_l) = 0`
and `h(x_k, y_l) = δ_{kl}`, completes them by a basis of their orthogonal complement, and
deduces an invertible `P` and a weight function `w : n → ℤ^r` such that the Gram matrix
`P H ᵗP^σ` is supported where the weights add up to zero, the weights add up to zero, and
every standard basis vector of `ℤ^r` is a weight.
-/

noncomputable section

universe u v

open Matrix

namespace Langlands.GroupScheme.AntihermitianSplitRank

open Quaternionic Quaternionic.FirstKindInvolution

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  (σ : FirstKindInvolution K D) {n : Type} [Fintype n] [DecidableEq n]

/-! ### Elementary identities for the form -/

section Sums

omit [DecidableEq n] in
theorem sesqForm_sum_left (H : Matrix n n D) {ι : Type*} (s : Finset ι) (f : ι → n → D)
    (y : n → D) : σ.sesqForm H (∑ i ∈ s, f i) y = ∑ i ∈ s, σ.sesqForm H (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, σ.sesqForm_add_left, ih]

omit [DecidableEq n] in
theorem sesqForm_sum_right (H : Matrix n n D) {ι : Type*} (s : Finset ι) (x : n → D)
    (f : ι → n → D) : σ.sesqForm H x (∑ i ∈ s, f i) = ∑ i ∈ s, σ.sesqForm H x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, σ.sesqForm_add_right, ih]

omit [DecidableEq n] in
theorem sesqForm_sub_left (H : Matrix n n D) (x x' y : n → D) :
    σ.sesqForm H (x - x') y = σ.sesqForm H x y - σ.sesqForm H x' y := by
  simp [sesqForm, sub_mul, Finset.sum_sub_distrib]

omit [DecidableEq n] in
theorem sesqForm_sub_right (H : Matrix n n D) (x y y' : n → D) :
    σ.sesqForm H x (y - y') = σ.sesqForm H x y - σ.sesqForm H x y' := by
  simp [sesqForm, mul_sub, Finset.sum_sub_distrib]

/-- **Representation of linear forms.** For invertible `H`, every left `D`-linear form on
`D^n` is `v ↦ h(v, z)` for some `z`. -/
theorem exists_sesqForm_eq_apply {H : Matrix n n D} (hu : IsUnit H)
    (f : (n → D) →ₗ[D] D) : ∃ z : n → D, ∀ v, σ.sesqForm H v z = f v := by
  let c : n → D := fun i => f (Pi.single i 1)
  refine ⟨σ ∘ (((hu.unit⁻¹ : (Matrix n n D)ˣ) : Matrix n n D) *ᵥ c), fun v => ?_⟩
  have h1 : (σ ∘ (σ ∘ (((hu.unit⁻¹ : (Matrix n n D)ˣ) : Matrix n n D) *ᵥ c))) =
      ((hu.unit⁻¹ : (Matrix n n D)ˣ) : Matrix n n D) *ᵥ c := by
    funext i
    simp
  rw [σ.sesqForm_eq_dotProduct, h1, Matrix.mulVec_mulVec, hu.mul_val_inv, Matrix.one_mulVec]
  have hv : v = ∑ i, v i • Pi.single i (1 : D) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    refine Finset.sum_congr rfl fun i _ => ?_
    funext j
    by_cases h : j = i
    · subst h
      simp
    · simp [h]
  conv_rhs => rw [hv]
  rw [_root_.map_sum]
  simp only [LinearMap.map_smul, smul_eq_mul, dotProduct, c]

end Sums

/-! ### Hyperbolic families -/

section Hyperbolic

variable [LinearOrder n]

omit [LinearOrder n] in
variable {σ} in
/-- The form takes the value `-δ_{kl}` on a reversed dual pair. -/
theorem sesqForm_swap_ite {H : Matrix n n D} (hH : σ.IsAntihermitian H) {r : ℕ}
    {x y : Fin r → n → D} (hxy : ∀ k l, σ.sesqForm H (x k) (y l) = if k = l then 1 else 0)
    (k l : Fin r) : σ.sesqForm H (y l) (x k) = -(if k = l then 1 else 0) := by
  rw [IsAntihermitian.sesqForm_swap σ hH, hxy]
  split_ifs <;> simp

variable {σ} in
/-- **Hyperbolic families.** A nondegenerate trace-valued antihermitian form of Witt index `r`
has vectors `x₁, …, x_r, y₁, …, y_r` with `h(x_k, x_l) = h(y_k, y_l) = 0` and
`h(x_k, y_l) = δ_{kl}`. -/
theorem exists_hyperbolic_family {H : Matrix n n D} (hH : σ.IsAntihermitian H)
    (hu : IsUnit H) :
    ∃ x y : Fin (σ.wittIndex H) → n → D,
      (∀ k l, σ.sesqForm H (x k) (x l) = 0) ∧ (∀ k l, σ.sesqForm H (y k) (y l) = 0) ∧
      (∀ k l, σ.sesqForm H (x k) (y l) = if k = l then 1 else 0) := by
  classical
  set r := σ.wittIndex H
  let W := σ.wittSubspace H
  let bW : Module.Basis (Fin r) D W := Module.finBasisOfFinrankEq D W (σ.finrank_wittSubspace H)
  let x : Fin r → n → D := fun k => (bW k : n → D)
  have hxx : ∀ k l, σ.sesqForm H (x k) (x l) = 0 := fun k l =>
    σ.isTotallyIsotropic_wittSubspace H _ (bW k).2 _ (bW l).2
  choose g hg using fun l : Fin r => LinearMap.exists_extend (bW.coord l)
  choose z hz using fun l : Fin r => exists_sesqForm_eq_apply σ hu (g l)
  have hxz : ∀ k l, σ.sesqForm H (x k) (z l) = if k = l then 1 else 0 := by
    intro k l
    rw [hz l]
    have h1 : g l (x k) = (g l).comp W.subtype (bW k) := rfl
    rw [h1, hg l, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  have hzx : ∀ k l, σ.sesqForm H (z l) (x k) = -(if k = l then 1 else 0) :=
    sesqForm_swap_ite hH hxz
  let gz : Matrix (Fin r) (Fin r) D := Matrix.of fun l l' => σ.sesqForm H (z l) (z l')
  have hgz : σ.IsAntihermitian gz := by
    refine ⟨?_, fun l => sesqForm_self_mem_alternatingSubspace hH (z l)⟩
    ext l l'
    simp only [matrix_apply, gz, Matrix.of_apply, Matrix.neg_apply]
    rw [IsAntihermitian.sesqForm_swap σ hH, FirstKindInvolution.map_neg,
      FirstKindInvolution.apply_apply]
  obtain ⟨A, hA⟩ := exists_eq_sub_matrix hgz
  have hA' : ∀ l l', σ.sesqForm H (z l) (z l') = A l l' - σ (A l' l) := by
    intro l l'
    have := congrFun (congrFun hA l) l'
    simpa [gz] using this
  let y : Fin r → n → D := fun l => z l - ∑ k, A l k • x k
  have hxy : ∀ k l, σ.sesqForm H (x k) (y l) = if k = l then 1 else 0 := by
    intro k l
    simp only [y, sesqForm_sub_right, sesqForm_sum_right, σ.sesqForm_smul_right, hxx, zero_mul,
      Finset.sum_const_zero, sub_zero, hxz]
  refine ⟨x, y, hxx, fun l l' => ?_, hxy⟩
  simp only [y, sesqForm_sub_left, sesqForm_sub_right, sesqForm_sum_left, sesqForm_sum_right,
    σ.sesqForm_smul_left, σ.sesqForm_smul_right, hxx, hzx, hxz, mul_zero, Finset.sum_const_zero,
    sub_zero, hA']
  simp only [mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul, neg_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_neg_distrib]
  abel

end Hyperbolic

/-! ### Witt bases -/

section WittBasis

variable [LinearOrder n]

variable {σ} in
/-- **Witt bases.** For an invertible trace-valued antihermitian `H` of Witt index `r` there are
an invertible `P` and weights `w : n → ℤ^r` such that `P H ᵗP^σ` is supported where the weights
add up to zero, the weights add up to zero, and every standard basis vector of `ℤ^r` is a
weight. -/
theorem exists_wittBasis {H : Matrix n n D} (hH : σ.IsAntihermitian H) (hu : IsUnit H) :
    ∃ (P : Matrix n n D) (w : n → Fin (σ.wittIndex H) → ℤ), IsUnit P ∧
      (∀ i j, (P * H * σ.matrix n P) i j ≠ 0 → w i + w j = 0) ∧ ∑ i, w i = 0 ∧
      ∀ k, ∃ i, w i = Pi.single k 1 := by
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
  -- the weights
  let W : (Fin r ⊕ Fin r) ⊕ Fin d → Fin r → ℤ :=
    Sum.elim (Sum.elim (fun k => Pi.single k 1) fun k => -Pi.single k 1) fun _ => 0
  refine ⟨P, fun i => W (e i), hP, ?_, ?_, ?_⟩
  · have key : ∀ s t, σ.sesqForm H (p s) (p t) ≠ 0 → W s + W t = 0 := by
      rintro ((k | k) | a) ((l | l) | b) h
      · exact absurd (hxx k l) h
      · have hkl : k = l := by
          by_contra hkl
          apply h
          change σ.sesqForm H (x k) (y l) = 0
          rw [hxy, ite_eq_right hkl]
        subst hkl
        simp [W]
      · exact absurd (hxU b k) h
      · have hkl : l = k := by
          by_contra hkl
          apply h
          change σ.sesqForm H (y k) (x l) = 0
          rw [hyx, ite_eq_right hkl, neg_zero]
        subst hkl
        simp [W]
      · exact absurd (hyy k l) h
      · exact absurd (hyU b k) h
      · exact absurd (hUx a l) h
      · exact absurd (hUy a l) h
      · simp [W]
    intro i j hij
    rw [mul_mul_matrix_apply] at hij
    exact key (e i) (e j) hij
  · rw [Equiv.sum_comp e W]
    simp [W, Fintype.sum_sum_type]
  · intro k
    exact ⟨e.symm (Sum.inl (Sum.inl k)), by simp [W]⟩

end WittBasis

end Langlands.GroupScheme.AntihermitianSplitRank
