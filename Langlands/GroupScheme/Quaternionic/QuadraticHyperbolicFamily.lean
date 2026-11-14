import Langlands.GroupScheme.Quaternionic.HyperbolicScalingMatrix
import Langlands.GroupScheme.Quaternionic.HyperbolicPair
import Langlands.GroupScheme.Quaternionic.QuadraticFormIdentities

/-! # Hyperbolic families of a nondegenerate quaternionic quadratic form -/

noncomputable section

universe u v

open scoped Matrix

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  (σ : FirstKindInvolution K D) {n : Type} [Fintype n] [DecidableEq n]

/-- A family of hyperbolic pairs `(xₖ, yₖ)` for `q` which are mutually orthogonal for the polar
form `h`: `q(xₖ) = q(yₖ) = 0`, `h(xₖ, yₗ) = δₖₗ`, `h(xₖ, xₗ) = 0` and `h(yₖ, yₗ) = 0`. -/
structure IsHyperbolicFamily (q : σ.QuadraticForms n) {ι : Type*} [DecidableEq ι]
    (x y : ι → n → D) : Prop where
  quadraticValue_left : ∀ k, σ.quadraticValue (x k) q = 0
  quadraticValue_right : ∀ k, σ.quadraticValue (y k) q = 0
  polar_left_right : ∀ k l, σ.sesqForm (σ.polar q) (x k) (y l) = if k = l then 1 else 0
  polar_left_left : ∀ k l, σ.sesqForm (σ.polar q) (x k) (x l) = 0
  polar_right_right : ∀ k l, σ.sesqForm (σ.polar q) (y k) (y l) = 0

variable {σ}

/-! ### Sums in the sesquilinear form -/

theorem sesqForm_sum_smul_left (H : Matrix n n D) {ι : Type*} (s : Finset ι) (c : ι → D)
    (u : ι → n → D) (w : n → D) :
    σ.sesqForm H (∑ k ∈ s, c k • u k) w = ∑ k ∈ s, c k * σ.sesqForm H (u k) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, sesqForm_add_left, sesqForm_smul_left, ih]

theorem sesqForm_sum_smul_right (H : Matrix n n D) {ι : Type*} (s : Finset ι) (c : ι → D)
    (u : ι → n → D) (w : n → D) :
    σ.sesqForm H w (∑ k ∈ s, c k • u k) = ∑ k ∈ s, σ.sesqForm H w (u k) * σ (c k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, sesqForm_add_right, sesqForm_smul_right, ih]

/-- The polar form vanishes on a totally singular subspace. -/
theorem IsTotallySingular.sesqForm_polar_eq_zero {q : σ.QuadraticForms n}
    {W : Submodule D (n → D)} (hW : σ.IsTotallySingular q W) {u v : n → D} (hu : u ∈ W)
    (hv : v ∈ W) : σ.sesqForm (σ.polar q) u v = 0 := by
  apply σ.eq_zero_of_forall_mul_mem_alternatingSubspace
  intro a
  have h1 := σ.quadraticValue_add u (σ a • v) q
  rw [hW _ (W.add_mem hu (W.smul_mem _ hv)), hW u hu, hW _ (W.smul_mem _ hv), zero_add,
    zero_add, sesqForm_smul_right, apply_apply] at h1
  exact (Submodule.Quotient.mk_eq_zero _).mp h1.symm

/-! ### Dual families -/

/-- For a nondegenerate form, a linearly independent family `x` has a polar-dual family `z`:
`h(xₖ, zₗ) = δₖₗ`. -/
theorem exists_polar_dual_family (q : σ.QuadraticForms n) (hq : σ.IsNondegenerateQuadratic q)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → n → D) (hx : LinearIndependent D x) :
    ∃ z : ι → n → D, ∀ k l, σ.sesqForm (σ.polar q) (x k) (z l) = if k = l then 1 else 0 := by
  let Ψ : (n → D) →ₗ[D] (ι → D) := LinearMap.pi (fun k => σ.polarFunctional q (x k))
  have hΨ : ∀ z k, Ψ z k = σ.sesqForm (σ.polar q) z (x k) := fun z k => rfl
  have hsurj : LinearMap.range Ψ = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    let c : ι → D := fun k => f fun j => if k = j then 1 else 0
    have hfv : ∀ v : ι → D, f v = ∑ k, v k * c k := by
      intro v
      rw [LinearMap.pi_apply_eq_sum_univ f v]
      rfl
    have hzero : ∀ z, ∑ k, σ.sesqForm (σ.polar q) z (x k) * c k = 0 := by
      intro z
      have h1 := hf (LinearMap.mem_range_self Ψ z)
      rw [LinearMap.mem_ker, hfv] at h1
      exact h1
    let v : n → D := ∑ k, σ (c k) • x k
    have hv : ∀ z, σ.sesqForm (σ.polar q) v z = 0 := by
      intro z
      apply σ.injective
      rw [sesqForm_polar_swap, sesqForm_sum_smul_right, map_zero]
      simp only [apply_apply]
      exact hzero z
    have hv0 : v = 0 := by
      by_contra hv0
      obtain ⟨z, hz⟩ := σ.exists_polar_partner q hq v hv0
      rw [hv z] at hz
      exact zero_ne_one hz
    have hc : ∀ k, c k = 0 := by
      intro k
      have h1 := (Fintype.linearIndependent_iff.mp hx) (fun k => σ (c k)) hv0 k
      rw [← σ.apply_apply (c k), h1, map_zero]
    apply hf0
    refine LinearMap.ext fun w => ?_
    rw [hfv]
    simp [hc]
  have hex : ∀ l, ∃ z, Ψ z = Pi.single l 1 := by
    intro l
    have h1 : Pi.single l (1 : D) ∈ LinearMap.range Ψ := hsurj ▸ Submodule.mem_top
    exact h1
  choose z hz using hex
  refine ⟨z, fun k l => ?_⟩
  have h1 := congrFun (hz l) k
  rw [hΨ, Pi.single_apply] at h1
  rw [← sesqForm_polar_swap, h1]
  split_ifs <;> simp

/-! ### Existence of a hyperbolic family of length the Witt index -/

/-- A nondegenerate form has a hyperbolic family indexed by `Fin r`, where `r` is the quadratic
Witt index: a basis `x` of a maximal totally singular subspace together with a family `y`. -/
theorem exists_isHyperbolicFamily (q : σ.QuadraticForms n) (hq : σ.IsNondegenerateQuadratic q) :
    ∃ x y : Fin (σ.quadraticWittIndex q) → n → D, σ.IsHyperbolicFamily q x y := by
  obtain ⟨W, hW, hdim⟩ := σ.exists_maximal_totallySingular q
  set r := σ.quadraticWittIndex q
  let bW : Module.Basis (Fin r) D W := Module.finBasisOfFinrankEq D W hdim
  let x : Fin r → n → D := fun k => (bW k : n → D)
  have hxW : ∀ k, x k ∈ W := fun k => (bW k).2
  have hx : LinearIndependent D x := bW.linearIndependent.map' W.subtype W.ker_subtype
  have hxx : ∀ k l, σ.sesqForm (σ.polar q) (x k) (x l) = 0 := fun k l =>
    hW.sesqForm_polar_eq_zero (hxW k) (hxW l)
  obtain ⟨z, hz⟩ := exists_polar_dual_family q hq x hx
  have hzx : ∀ k p, σ.sesqForm (σ.polar q) (z k) (x p) = if p = k then 1 else 0 := by
    intro k p
    rw [← sesqForm_polar_swap, hz p k]
    split_ifs <;> simp
  let s : Fin r → D := fun l => Quotient.out (σ.quadraticValue (z l) q)
  have hs : ∀ l, (Submodule.Quotient.mk (s l) : D ⧸ σ.alternatingSubspace) =
      σ.quadraticValue (z l) q := fun l => Submodule.Quotient.mk_out _
  let c : Fin r → Fin r → D := fun l k =>
    if l < k then -σ.sesqForm (σ.polar q) (z l) (z k) else if l = k then -σ (s l) else 0
  let y : Fin r → n → D := fun l => z l + ∑ k, c l k • x k
  have hsumW : ∀ l, ∑ k, c l k • x k ∈ W := fun l =>
    W.sum_mem fun k _ => W.smul_mem _ (hxW k)
  have hxy : ∀ k l, σ.sesqForm (σ.polar q) (x k) (y l) = if k = l then 1 else 0 := by
    intro k l
    simp only [y]
    rw [sesqForm_add_right, sesqForm_sum_smul_right, hz]
    simp [hxx]
  have hyy : ∀ k l, σ.sesqForm (σ.polar q) (y k) (y l) =
      σ.sesqForm (σ.polar q) (z k) (z l) + σ (c l k) + c k l := by
    intro k l
    rw [show y k = z k + ∑ m, c k m • x m from rfl, sesqForm_add_left, sesqForm_sum_smul_left]
    simp only [hxy]
    rw [show y l = z l + ∑ m, c l m • x m from rfl, sesqForm_add_right, sesqForm_sum_smul_right]
    simp only [hzx, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hqy : ∀ l, σ.quadraticValue (y l) q = 0 := by
    intro l
    simp only [y]
    rw [quadraticValue_add, hW _ (hsumW l), ← hs l, sesqForm_sum_smul_right]
    simp only [hzx, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    simp only [c, lt_irrefl, ite_false, ite_true, map_neg, apply_apply]
    rw [add_zero, ← Submodule.Quotient.mk_add, add_neg_cancel, Submodule.Quotient.mk_zero]
  refine ⟨x, y, ⟨fun k => hW _ (hxW k), hqy, hxy, hxx, fun k l => ?_⟩⟩
  rcases lt_trichotomy k l with hkl | rfl | hkl
  · rw [hyy]
    simp only [c, hkl, ite_true, not_lt.mpr hkl.le, hkl.ne', ite_false, map_zero, add_zero]
    exact add_neg_cancel _
  · exact σ.sesqForm_polar_self_eq_zero q _ (hqy k)
  · rw [hyy]
    simp only [c, hkl, ite_true, not_lt.mpr hkl.le, hkl.ne', ite_false, map_neg, add_zero,
      sesqForm_polar_swap]
    exact add_neg_cancel _

namespace IsHyperbolicFamily

variable {q : σ.QuadraticForms n} {ι : Type*} [DecidableEq ι] {x y : ι → n → D}

/-- Reindexing a hyperbolic family along an injective map. -/
theorem comp (h : σ.IsHyperbolicFamily q x y) {ι' : Type*} [DecidableEq ι'] (e : ι' → ι)
    (he : Function.Injective e) : σ.IsHyperbolicFamily q (x ∘ e) (y ∘ e) where
  quadraticValue_left k := h.quadraticValue_left (e k)
  quadraticValue_right k := h.quadraticValue_right (e k)
  polar_left_right k l := by
    simp only [Function.comp_apply, h.polar_left_right, he.eq_iff]
  polar_left_left k l := h.polar_left_left (e k) (e l)
  polar_right_right k l := h.polar_right_right (e k) (e l)

/-- Each member of a hyperbolic family is a hyperbolic pair. -/
theorem isHyperbolicPair (h : σ.IsHyperbolicFamily q x y) (k : ι) :
    σ.IsHyperbolicPair q (x k) (y k) :=
  ⟨h.quadraticValue_left k, h.quadraticValue_right k,
    by rw [h.polar_left_right, ite_eq_left rfl]⟩

theorem polar_right_left (h : σ.IsHyperbolicFamily q x y) (k l : ι) :
    σ.sesqForm (σ.polar q) (y k) (x l) = if k = l then 1 else 0 := by
  rw [← sesqForm_polar_swap, h.polar_left_right]
  by_cases hkl : k = l
  · subst hkl; simp
  · simp [hkl, Ne.symm hkl]

end IsHyperbolicFamily

/-! ### Products of hyperbolic line matrices -/

theorem hyperbolicLineMatrix_mul_of_eq_zero (q : σ.QuadraticForms n) {a b c d : n → D}
    (had : σ.sesqForm (σ.polar q) a d = 0) :
    σ.hyperbolicLineMatrix q a b * σ.hyperbolicLineMatrix q c d = 0 := by
  apply Matrix.ext_of_single_vecMul
  intro i
  rw [← Matrix.vecMul_vecMul, vecMul_hyperbolicLineMatrix, vecMul_hyperbolicLineMatrix,
    sesqForm_smul_left, had, mul_zero, zero_smul, Matrix.vecMul_zero]

theorem hyperbolicLineMatrix_mul_of_eq_one (q : σ.QuadraticForms n) {a b c d : n → D}
    (had : σ.sesqForm (σ.polar q) a d = 1) :
    σ.hyperbolicLineMatrix q a b * σ.hyperbolicLineMatrix q c d =
      σ.hyperbolicLineMatrix q c b := by
  apply Matrix.ext_of_single_vecMul
  intro i
  rw [← Matrix.vecMul_vecMul, vecMul_hyperbolicLineMatrix, vecMul_hyperbolicLineMatrix,
    vecMul_hyperbolicLineMatrix, sesqForm_smul_left, had, mul_one]

namespace IsHyperbolicFamily

variable {q : σ.QuadraticForms n} {ι : Type*} [DecidableEq ι] {x y : ι → n → D}

theorem lineMatrix_mul_left_left (h : σ.IsHyperbolicFamily q x y) (k l : ι) :
    σ.hyperbolicLineMatrix q (x k) (y k) * σ.hyperbolicLineMatrix q (x l) (y l) =
      if k = l then σ.hyperbolicLineMatrix q (x k) (y k) else 0 := by
  by_cases hkl : k = l
  · subst hkl
    rw [ite_eq_left rfl,
      hyperbolicLineMatrix_mul_of_eq_one q (by rw [h.polar_left_right, ite_eq_left rfl])]
  · rw [ite_eq_right hkl,
      hyperbolicLineMatrix_mul_of_eq_zero q (by rw [h.polar_left_right, ite_eq_right hkl])]

theorem lineMatrix_mul_left_right (h : σ.IsHyperbolicFamily q x y) (k l : ι) :
    σ.hyperbolicLineMatrix q (x k) (y k) * σ.hyperbolicLineMatrix q (y l) (x l) = 0 :=
  hyperbolicLineMatrix_mul_of_eq_zero q (h.polar_left_left k l)

theorem lineMatrix_mul_right_left (h : σ.IsHyperbolicFamily q x y) (k l : ι) :
    σ.hyperbolicLineMatrix q (y k) (x k) * σ.hyperbolicLineMatrix q (x l) (y l) = 0 :=
  hyperbolicLineMatrix_mul_of_eq_zero q (h.polar_right_right k l)

theorem lineMatrix_mul_right_right (h : σ.IsHyperbolicFamily q x y) (k l : ι) :
    σ.hyperbolicLineMatrix q (y k) (x k) * σ.hyperbolicLineMatrix q (y l) (x l) =
      if k = l then σ.hyperbolicLineMatrix q (y k) (x k) else 0 := by
  by_cases hkl : k = l
  · subst hkl
    rw [ite_eq_left rfl,
      hyperbolicLineMatrix_mul_of_eq_one q (by rw [h.polar_right_left, ite_eq_left rfl])]
  · rw [ite_eq_right hkl,
      hyperbolicLineMatrix_mul_of_eq_zero q (by rw [h.polar_right_left, ite_eq_right hkl])]

theorem lineMatrix_ne_zero (h : σ.IsHyperbolicFamily q x y) (k : ι) :
    σ.hyperbolicLineMatrix q (x k) (y k) ≠ 0 := by
  intro h0
  have h1 := vecMul_hyperbolicLineMatrix σ q (x k) (y k) (x k)
  rw [h0, Matrix.vecMul_zero, h.polar_left_right, ite_eq_left rfl, one_smul] at h1
  exact (h.isHyperbolicPair k).left_ne_zero h1.symm

end IsHyperbolicFamily

/-! ### Congruence identities for one hyperbolic pair -/

namespace IsHyperbolicPair

variable {q : σ.QuadraticForms n} {x y : n → D}

private theorem mk_congr_eq_pullback (Q : Matrix n n D)
    (hQ : (Submodule.Quotient.mk Q : σ.QuadraticForms n) = q) (M : Matrix n n D) :
    (Submodule.Quotient.mk (M * Q * σ.matrix n M) : σ.QuadraticForms n) =
      σ.quadraticPullback M q := by
  rw [← hQ]
  rfl

/-- For a hyperbolic pair `(x, y)` and `P = (z ↦ h(z, y) x)`, the matrix `P Q ᵗP^σ` lies in
`{X - ᵗX^σ}`. -/
theorem lineMatrix_congr_mem (h : σ.IsHyperbolicPair q x y) (Q : Matrix n n D)
    (hQ : (Submodule.Quotient.mk Q : σ.QuadraticForms n) = q) :
    σ.hyperbolicLineMatrix q x y * Q * σ.matrix n (σ.hyperbolicLineMatrix q x y) ∈
      σ.quadraticKernel n := by
  apply (Submodule.Quotient.mk_eq_zero _).mp
  rw [mk_congr_eq_pullback Q hQ]
  apply σ.eq_zero_of_forall_quadraticValue_eq_zero
  intro z
  rw [quadraticValue_pullback, vecMul_hyperbolicLineMatrix]
  exact σ.quadraticValue_smul_eq_zero _ _ q h.1

/-- For a hyperbolic pair `(x, y)`, `P = (z ↦ h(z, y) x)` and `P' = (z ↦ h(z, x) y)`, the matrix
`P Q + Q ᵗP^σ - P Q ᵗP'^σ - P' Q ᵗP^σ` lies in `{X - ᵗX^σ}`. -/
theorem lineMatrix_polar_mem (h : σ.IsHyperbolicPair q x y) (Q : Matrix n n D)
    (hQ : (Submodule.Quotient.mk Q : σ.QuadraticForms n) = q) :
    σ.hyperbolicLineMatrix q x y * Q + Q * σ.matrix n (σ.hyperbolicLineMatrix q x y) -
        σ.hyperbolicLineMatrix q x y * Q * σ.matrix n (σ.hyperbolicLineMatrix q y x) -
        σ.hyperbolicLineMatrix q y x * Q * σ.matrix n (σ.hyperbolicLineMatrix q x y) ∈
      σ.quadraticKernel n := by
  set P := σ.hyperbolicLineMatrix q x y
  set P' := σ.hyperbolicLineMatrix q y x
  have key : P * Q + Q * σ.matrix n P - P * Q * σ.matrix n P' - P' * Q * σ.matrix n P =
      (1 + P) * Q * σ.matrix n (1 + P) - Q - (P + P') * Q * σ.matrix n (P + P') +
        P' * Q * σ.matrix n P' := by
    simp only [FirstKindInvolution.map_add, FirstKindInvolution.map_one]
    noncomm_ring
  rw [key]
  apply (Submodule.Quotient.mk_eq_zero _).mp
  rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub,
    mk_congr_eq_pullback Q hQ, mk_congr_eq_pullback Q hQ, mk_congr_eq_pullback Q hQ, hQ]
  apply σ.eq_zero_of_forall_quadraticValue_eq_zero
  intro z
  rw [LinearMap.map_add, LinearMap.map_sub, LinearMap.map_sub, quadraticValue_pullback,
    quadraticValue_pullback, quadraticValue_pullback, Matrix.vecMul_add, Matrix.vecMul_add,
    Matrix.vecMul_one, vecMul_hyperbolicLineMatrix, vecMul_hyperbolicLineMatrix,
    quadraticValue_add, σ.quadraticValue_smul_eq_zero _ _ q h.1,
    h.quadraticValue_plane, σ.quadraticValue_smul_eq_zero _ _ q h.2.1, sesqForm_smul_right]
  have hswap : (Submodule.Quotient.mk (σ.sesqForm (σ.polar q) z y *
      σ (σ.sesqForm (σ.polar q) z x)) : D ⧸ σ.alternatingSubspace) =
      Submodule.Quotient.mk (σ.sesqForm (σ.polar q) z x * σ (σ.sesqForm (σ.polar q) z y)) := by
    rw [← quotient_mk_map, map_mul, apply_apply]
  rw [hswap]
  abel

end IsHyperbolicPair

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
