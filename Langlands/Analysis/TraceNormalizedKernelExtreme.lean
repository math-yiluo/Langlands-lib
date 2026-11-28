import Langlands.Analysis.TraceNormalizedKernelCone
import Mathlib.Algebra.Star.StarProjection

/-! # Extreme points of the trace-normalized kernel set

A cone element `F` (`Langlands.Analysis.KernelCone.IsConeElement`) defines a positive kernel on
`𝒜 × κ × W`; its Hilbert space `Space hF` carries vectors `vec hF x k w` with
`⟪vec hF x k w, vec hF y k' w'⟫ = F (k, k', x^* y, w, w')` and a `*`-representation `rho hF` of
`𝒜` by left multiplication. For an orthogonal projection `Q` commuting with `rho hF`, the
*compression* `F_Q (k, k', x, w, w') = ⟪Q (vec hF 1 k w), vec hF x k' w'⟫` is again a cone element,
and `F = F_Q + F_{1 - Q}`. For strictly positive weights `c` (`∀ k, 0 < c k`), the weighted trace
`traceW` is additive on cone elements and faithful on bounded cone elements, and a bounded cone
element of finite weighted trace is bounded pointwise by it. Consequently, for strictly positive
weights `c` and a nonzero extreme point `F` of `coneSet Rel c e`, every such projection is `0`
or `1`.
-/

noncomputable section

open scoped ComplexConjugate InnerProductSpace ENNReal
open Filter Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Analysis.KernelCone

variable {𝒜 : Type*} [NormedRing 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜]
variable {κ : Type*}
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
variable {Rel : Set (κ × 𝒜 × κ × (W →L[ℂ] W))} {F : Coord 𝒜 κ W → ℂ}

/-! ### The Hilbert space of a cone element -/

section GNS

variable (hF : IsConeElement Rel F)

/-- The positive kernel of a cone element. -/
def kernel : PositiveKernel (𝒜 × κ × W) where
  toFun := kernelOf F
  conj_symm' i j := by
    have h := hF.herm i.2.1 j.2.1 (star i.1 * j.1) i.2.2 j.2.2
    simpa [kernelOf, pt, star_mul, star_star] using h
  re_nonneg' := hF.pos

/-- The Hilbert space of a cone element. -/
abbrev Space : Type _ := (kernel hF).Space

/-- The vector of an index. -/
def vec (x : 𝒜) (k : κ) (w : W) : Space hF := (kernel hF).vec (x, k, w)

theorem inner_vec (x : 𝒜) (k : κ) (w : W) (y : 𝒜) (k' : κ) (w' : W) :
    ⟪vec hF x k w, vec hF y k' w'⟫_ℂ = F (k, k', star x * y, w, w') :=
  (kernel hF).inner_vec_vec _ _

theorem ext_vec {u v : Space hF}
    (h : ∀ y k' w', ⟪u, vec hF y k' w'⟫_ℂ = ⟪v, vec hF y k' w'⟫_ℂ) : u = v :=
  (kernel hF).ext_inner_vec fun j => h j.1 j.2.1 j.2.2

theorem clm_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A B : Space hF →L[ℂ] E} (h : ∀ x k w, A (vec hF x k w) = B (vec hF x k w)) : A = B :=
  (kernel hF).clm_ext_vec fun i => h i.1 i.2.1 i.2.2

theorem vec_add (x y : 𝒜) (k : κ) (w : W) :
    vec hF (x + y) k w = vec hF x k w + vec hF y k w := by
  refine ext_vec hF fun z k' w' => ?_
  rw [inner_add_left, inner_vec, inner_vec, inner_vec, star_add, add_mul, hF.add_mid]

theorem vec_smul (r : ℂ) (x : 𝒜) (k : κ) (w : W) :
    vec hF (r • x) k w = r • vec hF x k w := by
  refine ext_vec hF fun z k' w' => ?_
  rw [inner_smul_left, inner_vec, inner_vec, star_smul, smul_mul_assoc, hF.smul_mid]
  rfl

theorem vec_add_w (x : 𝒜) (k : κ) (w₁ w₂ : W) :
    vec hF x k (w₁ + w₂) = vec hF x k w₁ + vec hF x k w₂ := by
  refine ext_vec hF fun z k' w' => ?_
  rw [inner_add_left, inner_vec, inner_vec, inner_vec, hF.add_left]

theorem vec_smul_w (x : 𝒜) (k : κ) (r : ℂ) (w : W) :
    vec hF x k (r • w) = r • vec hF x k w := by
  refine ext_vec hF fun z k' w' => ?_
  rw [inner_smul_left, inner_vec, inner_vec, hF.smul_left]

/-- Left multiplication by `a`. -/
def rho (a : 𝒜) : Space hF →L[ℂ] Space hF :=
  (kernel hF).opOfMap (kernel hF) (lmul a) ‖a‖ (norm_nonneg a) (fun f => hF.mul_le a f)

theorem rho_vec (a x : 𝒜) (k : κ) (w : W) : rho hF a (vec hF x k w) = vec hF (a * x) k w :=
  (kernel hF).opOfMap_vec (kernel hF) _ _ _ _ _

theorem norm_rho_le (a : 𝒜) : ‖rho hF a‖ ≤ ‖a‖ :=
  (kernel hF).opOfMap_norm_le (kernel hF) _ _ _ _

theorem inner_rho_vec (a x : 𝒜) (k : κ) (w : W) (y : 𝒜) (k' : κ) (w' : W) :
    ⟪rho hF a (vec hF x k w), vec hF y k' w'⟫_ℂ =
      ⟪vec hF x k w, rho hF (star a) (vec hF y k' w')⟫_ℂ := by
  rw [rho_vec, rho_vec, inner_vec, inner_vec, star_mul, mul_assoc]

theorem adjoint_rho (a : 𝒜) : ContinuousLinearMap.adjoint (rho hF a) = rho hF (star a) := by
  refine clm_ext hF fun x k w => ext_vec hF fun y k' w' => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, ← inner_conj_symm, inner_rho_vec, inner_conj_symm]

theorem inner_rho (a : 𝒜) (u v : Space hF) :
    ⟪rho hF a u, v⟫_ℂ = ⟪u, rho hF (star a) v⟫_ℂ := by
  rw [← adjoint_rho, ContinuousLinearMap.adjoint_inner_right]

theorem rho_mul (a b : 𝒜) : rho hF (a * b) = rho hF a * rho hF b := by
  refine clm_ext hF fun x k w => ?_
  rw [mul_apply_eq_comp, rho_vec, rho_vec, rho_vec, mul_assoc]

theorem rho_one : rho hF 1 = 1 := by
  refine clm_ext hF fun x k w => ?_
  rw [rho_vec, one_mul, one_apply_eq_self]

theorem norm_vec_sq (x : 𝒜) (k : κ) (w : W) :
    ‖vec hF x k w‖ ^ 2 = (F (k, k, star x * x, w, w)).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_vec]
  rfl

omit hF in
theorem re_diag_nonneg (hF : IsConeElement Rel F) (k : κ) (w : W) : 0 ≤ (F (k, k, 1, w, w)).re := by
  have h := norm_vec_sq hF 1 k w
  rw [star_one, one_mul] at h
  rw [← h]
  positivity

theorem vec_rel {r : κ × 𝒜 × κ × (W →L[ℂ] W)} (hr : r ∈ Rel) (w : W) :
    vec hF (star r.2.1) r.1 w = vec hF 1 r.2.2.1 (r.2.2.2 w) := by
  refine ext_vec hF fun y k' w' => ?_
  rw [inner_vec, inner_vec, star_star, star_one, one_mul, hF.rel r hr]

variable (hB : IsBoundedForm F)

/-- The bounded operator `w ↦ vec hF x k w`. -/
def vecL (x : 𝒜) (k : κ) : W →L[ℂ] Space hF :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun w => vec hF x k w
      map_add' := vec_add_w hF x k
      map_smul' := fun r w => vec_smul_w hF x k r w }
    (by
      obtain ⟨M, hM⟩ := hB k k (star x * x)
      refine ⟨Real.sqrt (max M 0), fun w => ?_⟩
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      have h1 : ‖vec hF x k w‖ ^ 2 ≤ max M 0 * ‖w‖ ^ 2 := by
        rw [norm_vec_sq]
        calc (F (k, k, star x * x, w, w)).re ≤ ‖F (k, k, star x * x, w, w)‖ :=
              Complex.re_le_norm _
          _ ≤ M * (‖w‖ * ‖w‖) := hM w w
          _ ≤ max M 0 * ‖w‖ ^ 2 := by
              rw [← sq]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
      rw [← Real.sqrt_sq (norm_nonneg (vec hF x k w)), ← Real.sqrt_sq (norm_nonneg w),
        ← Real.sqrt_mul (le_max_right _ _)]
      exact Real.sqrt_le_sqrt h1)

@[simp]
theorem vecL_apply (x : 𝒜) (k : κ) (w : W) : vecL hF hB x k w = vec hF x k w := rfl

end GNS

/-! ### Compressions -/

section Compress

variable (hF : IsConeElement Rel F)

/-- The compression `F_Q (k, k', x, w, w') = ⟪Q (vec 1 k w), vec x k' w'⟫`. -/
def compress (Q : Space hF →L[ℂ] Space hF) : Coord 𝒜 κ W → ℂ :=
  fun p => ⟪Q (vec hF 1 p.1 p.2.2.2.1), vec hF p.2.2.1 p.2.1 p.2.2.2.2⟫_ℂ

theorem compress_one : compress hF 1 = F := by
  funext p
  obtain ⟨k, k', x, w, w'⟩ := p
  simp only [compress, one_apply_eq_self, inner_vec, star_one, one_mul]

theorem compress_add (Q₁ Q₂ : Space hF →L[ℂ] Space hF) :
    compress hF (Q₁ + Q₂) = compress hF Q₁ + compress hF Q₂ := by
  funext p
  simp only [compress, add_apply, inner_add_left, Pi.add_apply]

theorem compress_one_sub (Q : Space hF →L[ℂ] Space hF) :
    compress hF (1 - Q) = F - compress hF Q := by
  funext p
  obtain ⟨k, k', x, w, w'⟩ := p
  simp only [compress, sub_apply, inner_sub_left, Pi.sub_apply, one_apply_eq_self, inner_vec,
    star_one, one_mul]

variable {Q : Space hF →L[ℂ] Space hF}

theorem kernelOf_compress (hQc : ∀ a, Commute Q (rho hF a)) (i j : 𝒜 × κ × W) :
    kernelOf (compress hF Q) i j =
      ⟪Q (vec hF i.1 i.2.1 i.2.2), vec hF j.1 j.2.1 j.2.2⟫_ℂ := by
  change ⟪Q (vec hF 1 i.2.1 i.2.2), vec hF (star i.1 * j.1) j.2.1 j.2.2⟫_ℂ = _
  rw [← rho_vec, ← inner_rho, ← mul_apply_eq_comp, ← (hQc i.1).eq, mul_apply_eq_comp, rho_vec,
    mul_one]

theorem re_inner_proj_self (hQ : IsStarProjection Q) (ξ : Space hF) :
    (⟪Q ξ, ξ⟫_ℂ).re = ‖Q ξ‖ ^ 2 := by
  have h : ⟪Q ξ, ξ⟫_ℂ = ⟪Q ξ, Q ξ⟫_ℂ := by
    conv_lhs => rw [← hQ.isIdempotentElem.eq, mul_apply_eq_comp]
    exact (hQ.isSelfAdjoint.isSymmetric (Q ξ) ξ)
  rw [h]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (Q ξ)).symm

theorem isConeElement_compress (hQ : IsStarProjection Q) (hQc : ∀ a, Commute Q (rho hF a)) :
    IsConeElement Rel (compress hF Q) where
  add_mid k k' x y w w' := by simp only [compress, vec_add, inner_add_right]
  smul_mid k k' r x w w' := by simp only [compress, vec_smul, inner_smul_right]
  add_left k k' x w₁ w₂ w' := by simp only [compress, vec_add_w, map_add, inner_add_left]
  smul_left k k' x r w w' := by simp only [compress, vec_smul_w, map_smul, inner_smul_left]
  add_right k k' x w w₁ w₂ := by simp only [compress, vec_add_w, inner_add_right]
  smul_right k k' x w r w' := by simp only [compress, vec_smul_w, inner_smul_right]
  herm k k' x w w' := by
    simp only [compress]
    have h1 : vec hF (star x) k w = rho hF (star x) (vec hF 1 k w) := by rw [rho_vec, mul_one]
    have h2 : vec hF x k' w' = rho hF x (vec hF 1 k' w') := by rw [rho_vec, mul_one]
    rw [inner_conj_symm, h1, h2, inner_rho, star_star, ← mul_apply_eq_comp, ← (hQc x).eq,
      mul_apply_eq_comp]
    exact (hQ.isSelfAdjoint.isSymmetric _ _).symm
  pos f := by
    have e : kernelOf (compress hF Q) =
        fun i j => ⟪Q (vec hF i.1 i.2.1 i.2.2), vec hF j.1 j.2.1 j.2.2⟫_ℂ := by
      funext i j; exact kernelOf_compress hF hQc i j
    rw [e, kernelForm_inner, re_inner_proj_self hF hQ]
    positivity
  mul_le a f := by
    have e : kernelOf (compress hF Q) =
        fun i j => ⟪Q (vec hF i.1 i.2.1 i.2.2), vec hF j.1 j.2.1 j.2.2⟫_ℂ := by
      funext i j; exact kernelOf_compress hF hQc i j
    have e' : (fun i j => kernelOf (compress hF Q) (lmul a i) (lmul a j)) =
        fun i j => ⟪Q (rho hF a (vec hF i.1 i.2.1 i.2.2)),
          rho hF a (vec hF j.1 j.2.1 j.2.2)⟫_ℂ := by
      funext i j
      rw [kernelOf_compress hF hQc, rho_vec, rho_vec]
      rfl
    rw [e', e, kernelForm_inner, kernelForm_inner, re_inner_proj_self hF hQ,
      re_inner_proj_self hF hQ]
    set ξ := f.sum fun i b => b • vec hF i.1 i.2.1 i.2.2
    have hξ : (f.sum fun i b => b • rho hF a (vec hF i.1 i.2.1 i.2.2)) = rho hF a ξ := by
      rw [map_finsuppSum]
      simp only [map_smul]
    rw [hξ, ← mul_apply_eq_comp, (hQc a).eq, mul_apply_eq_comp]
    calc ‖rho hF a (Q ξ)‖ ^ 2 ≤ (‖rho hF a‖ * ‖Q ξ‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) ((rho hF a).le_opNorm _) 2
      _ ≤ (‖a‖ * ‖Q ξ‖) ^ 2 :=
          pow_le_pow_left₀ (by positivity)
            (mul_le_mul_of_nonneg_right (norm_rho_le hF a) (norm_nonneg _)) 2
      _ = ‖a‖ ^ 2 * ‖Q ξ‖ ^ 2 := by ring
  rel r hr k' x w w' := by
    simp only [compress]
    have h1 : vec hF (r.2.1 * x) k' w' = rho hF r.2.1 (vec hF x k' w') := (rho_vec ..).symm
    have h2 : ⟪Q (vec hF 1 r.1 w), rho hF r.2.1 (vec hF x k' w')⟫_ℂ =
        ⟪rho hF (star r.2.1) (Q (vec hF 1 r.1 w)), vec hF x k' w'⟫_ℂ := by
      rw [inner_rho, star_star]
    rw [h1, h2, ← mul_apply_eq_comp, ← (hQc (star r.2.1)).eq, mul_apply_eq_comp, rho_vec,
      mul_one, vec_rel hF hr]

theorem isBoundedForm_compress (hB : IsBoundedForm F) (Q : Space hF →L[ℂ] Space hF) :
    IsBoundedForm (compress hF Q) := by
  intro k k' x
  refine ⟨‖Q‖ * ‖vecL hF hB 1 k‖ * ‖vecL hF hB x k'‖, fun w w' => ?_⟩
  simp only [compress]
  calc ‖⟪Q (vec hF 1 k w), vec hF x k' w'⟫_ℂ‖ ≤ ‖Q (vec hF 1 k w)‖ * ‖vec hF x k' w'‖ :=
        norm_inner_le_norm _ _
    _ ≤ (‖Q‖ * (‖vecL hF hB 1 k‖ * ‖w‖)) * (‖vecL hF hB x k'‖ * ‖w'‖) := by
        refine mul_le_mul ((Q.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)))
          ((vecL hF hB x k').le_opNorm w') (norm_nonneg _) (by positivity)
        exact (vecL hF hB 1 k).le_opNorm w
    _ = _ := by ring

end Compress

/-! ### Weighted traces -/

section Trace

variable {β : Type*} (c : κ → ℝ) (e : HilbertBasis β ℂ W)

/-- The weighted trace `∑_{k,b} ENNReal.ofReal (c_k Re F (k, k, 1, e_b, e_b))` in `ℝ≥0∞`; each
summand is clipped to `[0, ∞)` separately. -/
def traceW (F : Coord 𝒜 κ W → ℂ) : ℝ≥0∞ :=
  ∑' p : κ × β, ENNReal.ofReal (c p.1 * (F (p.1, p.1, 1, e p.2, e p.2)).re)

/-- The trace `∑_b ENNReal.ofReal (Re F (k, k, 1, e_b, e_b))` in `ℝ≥0∞`; each summand is clipped to
`[0, ∞)` separately. -/
def traceK (F : Coord 𝒜 κ W → ℂ) (k : κ) : ℝ≥0∞ :=
  ∑' b : β, ENNReal.ofReal ((F (k, k, 1, e b, e b)).re)

variable {c e}

/-- The operator norm is at most the Hilbert–Schmidt norm on a Hilbert basis. -/
theorem opNorm_le_sqrt_tsum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : W →L[ℂ] E) (h : Summable fun i => ‖T (e i)‖ ^ 2) :
    ‖T‖ ≤ Real.sqrt (∑' i, ‖T (e i)‖ ^ 2) := by
  refine T.opNorm_le_bound (Real.sqrt_nonneg _) (fun x => ?_)
  have hx := T.hasSum (e.hasSum_repr x)
  simp only [map_smul] at hx
  refine le_of_tendsto hx.norm (Eventually.of_forall (fun s => ?_))
  have hnorm : ‖∑ i ∈ s, e.repr x i • T (e i)‖ ≤ ∑ i ∈ s, ‖e.repr x i‖ * ‖T (e i)‖ := by
    simpa only [norm_smul] using (norm_sum_le s (fun i => e.repr x i • T (e i)))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖e.repr x i‖) (fun i => ‖T (e i)‖)
  have hb : ∑ i ∈ s, ‖e.repr x i‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    simpa only [HilbertBasis.repr_apply_apply] using
      (e.orthonormal.sum_inner_products_le x (s := s))
  have ht : ∑ i ∈ s, ‖T (e i)‖ ^ 2 ≤ ∑' i, ‖T (e i)‖ ^ 2 :=
    h.sum_le_tsum s (fun _ _ => sq_nonneg _)
  have hs0 : 0 ≤ ∑ i ∈ s, ‖T (e i)‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsq : ‖∑ i ∈ s, e.repr x i • T (e i)‖ ^ 2 ≤
      (Real.sqrt (∑' i, ‖T (e i)‖ ^ 2) * ‖x‖) ^ 2 := by
    calc
      _ ≤ (∑ i ∈ s, ‖e.repr x i‖ * ‖T (e i)‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg
          (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))).2 hnorm
      _ ≤ (∑ i ∈ s, ‖e.repr x i‖ ^ 2) * ∑ i ∈ s, ‖T (e i)‖ ^ 2 := hcs
      _ ≤ ‖x‖ ^ 2 * ∑' i, ‖T (e i)‖ ^ 2 := mul_le_mul hb ht hs0 (sq_nonneg _)
      _ = _ := by
        rw [mul_pow, Real.sq_sqrt (tsum_nonneg (fun _ => sq_nonneg _))]
        ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1 hsq

variable (hF : IsConeElement Rel F) (hB : IsBoundedForm F)
include hF hB

theorem norm_vecL_le {k : κ} (hk : traceK e F k < ⊤) :
    ‖vecL hF hB 1 k‖ ≤ Real.sqrt (traceK e F k).toReal := by
  have hterm : ∀ b, ‖vecL hF hB 1 k (e b)‖ ^ 2 = (F (k, k, 1, e b, e b)).re := fun b => by
    rw [vecL_apply, norm_vec_sq, star_one, one_mul]
  have hfin : ∀ b, ENNReal.ofReal ((F (k, k, 1, e b, e b)).re) ≠ ⊤ := fun _ => ENNReal.ofReal_ne_top
  have hsum : Summable fun b => ‖vecL hF hB 1 k (e b)‖ ^ 2 := by
    have h := ENNReal.summable_toReal (f := fun b => ENNReal.ofReal ((F (k, k, 1, e b, e b)).re))
      hk.ne
    refine h.congr fun b => ?_
    rw [hterm, ENNReal.toReal_ofReal (re_diag_nonneg hF k (e b))]
  have htsum : (traceK e F k).toReal = ∑' b, ‖vecL hF hB 1 k (e b)‖ ^ 2 := by
    rw [traceK, ENNReal.tsum_toReal_eq hfin]
    refine tsum_congr fun b => ?_
    rw [hterm, ENNReal.toReal_ofReal (re_diag_nonneg hF k (e b))]
  rw [htsum]
  exact opNorm_le_sqrt_tsum _ hsum

theorem norm_le_traceK {k k' : κ} (hk : traceK e F k < ⊤) (hk' : traceK e F k' < ⊤) (x : 𝒜)
    (w w' : W) :
    ‖F (k, k', x, w, w')‖ ≤
      ‖x‖ * ‖w‖ * ‖w'‖ * Real.sqrt ((traceK e F k).toReal * (traceK e F k').toReal) := by
  have h1 : F (k, k', x, w, w') = ⟪vec hF 1 k w, rho hF x (vec hF 1 k' w')⟫_ℂ := by
    rw [rho_vec, mul_one, inner_vec, star_one, one_mul]
  rw [h1, Real.sqrt_mul ENNReal.toReal_nonneg]
  calc ‖⟪vec hF 1 k w, rho hF x (vec hF 1 k' w')⟫_ℂ‖
      ≤ ‖vec hF 1 k w‖ * ‖rho hF x (vec hF 1 k' w')‖ := norm_inner_le_norm _ _
    _ ≤ (Real.sqrt (traceK e F k).toReal * ‖w‖) *
          (‖x‖ * (Real.sqrt (traceK e F k').toReal * ‖w'‖)) := by
        refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
        · exact ((vecL hF hB 1 k).le_opNorm w).trans
            (mul_le_mul_of_nonneg_right (norm_vecL_le hF hB hk) (norm_nonneg _))
        · refine ((rho hF x).le_opNorm _).trans (mul_le_mul (norm_rho_le hF x) ?_
            (norm_nonneg _) (norm_nonneg _))
          exact ((vecL hF hB 1 k').le_opNorm w').trans
            (mul_le_mul_of_nonneg_right (norm_vecL_le hF hB hk') (norm_nonneg _))
    _ = _ := by ring

omit hF hB in
theorem ofReal_mul_traceK_le (hc : ∀ k, 0 < c k) (k : κ) :
    ENNReal.ofReal (c k) * traceK e F k ≤ traceW c e F := by
  rw [traceK, ← ENNReal.tsum_mul_left, traceW, ENNReal.tsum_prod']
  refine le_trans (le_of_eq ?_) (ENNReal.le_tsum k)
  refine tsum_congr fun b => ?_
  rw [ENNReal.ofReal_mul (hc k).le]

omit hF hB in
theorem traceK_lt_top (hc : ∀ k, 0 < c k) (hW : traceW c e F < ⊤) (k : κ) :
    traceK e F k < ⊤ := by
  have h := (ofReal_mul_traceK_le (F := F) (e := e) hc k).trans_lt hW
  exact ENNReal.lt_top_of_mul_ne_top_right h.ne (ENNReal.ofReal_pos.mpr (hc k)).ne'

omit hF hB in
theorem toReal_traceK_le (hc : ∀ k, 0 < c k) (hW : traceW c e F < ⊤) (k : κ) :
    (traceK e F k).toReal ≤ (traceW c e F).toReal / c k := by
  rw [le_div_iff₀ (hc k), mul_comm]
  have h := ofReal_mul_traceK_le (F := F) (e := e) hc k
  have h2 := ENNReal.toReal_mono hW.ne h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hc k).le] at h2

theorem norm_le_traceW (hc : ∀ k, 0 < c k) (hW : traceW c e F < ⊤) (k k' : κ) (x : 𝒜)
    (w w' : W) :
    ‖F (k, k', x, w, w')‖ ≤
      ‖x‖ * ‖w‖ * ‖w'‖ * ((traceW c e F).toReal / Real.sqrt (c k * c k')) := by
  refine (norm_le_traceK hF hB (traceK_lt_top hc hW k) (traceK_lt_top hc hW k') x w w').trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hN : 0 ≤ (traceW c e F).toReal := ENNReal.toReal_nonneg
  calc Real.sqrt ((traceK e F k).toReal * (traceK e F k').toReal)
      ≤ Real.sqrt (((traceW c e F).toReal / c k) * ((traceW c e F).toReal / c k')) :=
        Real.sqrt_le_sqrt (mul_le_mul (toReal_traceK_le hc hW k) (toReal_traceK_le hc hW k')
          ENNReal.toReal_nonneg (div_nonneg hN (hc k).le))
    _ = (traceW c e F).toReal / Real.sqrt (c k * c k') := by
        rw [div_mul_div_comm, Real.sqrt_div' _ (mul_pos (hc k) (hc k')).le,
          Real.sqrt_mul_self hN]

theorem traceW_zero_imp (hc : ∀ k, 0 < c k) (h0 : traceW c e F = 0) : F = 0 := by
  funext p
  obtain ⟨k, k', x, w, w'⟩ := p
  have hW : traceW c e F < ⊤ := by rw [h0]; exact ENNReal.zero_lt_top
  have h := norm_le_traceW hF hB hc hW k k' x w w'
  rw [h0, ENNReal.toReal_zero, zero_div, mul_zero] at h
  exact norm_le_zero_iff.mp h

omit hF hB in
theorem traceW_smul {t : ℝ} (ht : 0 ≤ t) : traceW c e (t • F) = ENNReal.ofReal t * traceW c e F := by
  rw [traceW, traceW, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun p => ?_
  rw [← ENNReal.ofReal_mul ht]
  congr 1
  simp only [Pi.smul_apply, Complex.real_smul, Complex.re_ofReal_mul]
  ring

end Trace

theorem traceW_add {β : Type*} {c : κ → ℝ} {e : HilbertBasis β ℂ W} (hc : ∀ k, 0 < c k)
    {F₁ F₂ : Coord 𝒜 κ W → ℂ} (h₁ : IsConeElement Rel F₁) (h₂ : IsConeElement Rel F₂) :
    traceW c e (F₁ + F₂) = traceW c e F₁ + traceW c e F₂ := by
  rw [traceW, traceW, traceW, ← ENNReal.tsum_add]
  refine tsum_congr fun p => ?_
  rw [← ENNReal.ofReal_add (mul_nonneg (hc p.1).le (re_diag_nonneg h₁ _ _))
    (mul_nonneg (hc p.1).le (re_diag_nonneg h₂ _ _))]
  congr 1
  simp only [Pi.add_apply, Complex.add_re]
  ring

/-! ### Membership in the compact set -/

theorem IsBoundedForm.smul {F : Coord 𝒜 κ W → ℂ} (hB : IsBoundedForm F) (t : ℝ) :
    IsBoundedForm (t • F) := by
  intro k k' x
  obtain ⟨M, hM⟩ := hB k k' x
  refine ⟨|t| * M, fun w w' => ?_⟩
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hM w w') (abs_nonneg t)

section Membership

variable {β : Type*} {c : κ → ℝ} {e : HilbertBasis β ℂ W} (hc : ∀ k, 0 < c k)
include hc

theorem traceW_le_one_iff (hC : IsConeElement Rel F) :
    traceW c e F ≤ 1 ↔ F ∈ traceSet c e := by
  change _ ↔ ∀ s : Finset (κ × β), _
  rw [traceW, ENNReal.tsum_eq_iSup_sum, iSup_le_iff]
  refine forall_congr' fun s => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun p _ => mul_nonneg (hc p.1).le (re_diag_nonneg hC _ _),
    ENNReal.ofReal_le_one]

theorem traceW_le_one_of_mem (hF : F ∈ coneSet Rel c e) : traceW c e F ≤ 1 :=
  (traceW_le_one_iff hc hF.1.1).mpr hF.1.2

omit hc in
theorem isBoundedForm_of_mem (hF : F ∈ coneSet Rel c e) : IsBoundedForm F := by
  intro k k' x
  refine ⟨‖x‖ / Real.sqrt (c k * c k'), fun w w' => ?_⟩
  refine (hF.2 k k' x w w').trans (le_of_eq ?_)
  ring

theorem mem_coneSet_of (hC : IsConeElement Rel F) (hB : IsBoundedForm F)
    (hW : traceW c e F ≤ 1) : F ∈ coneSet Rel c e := by
  refine ⟨⟨hC, (traceW_le_one_iff hc hC).mp hW⟩, fun k k' x w w' => ?_⟩
  have hlt : traceW c e F < ⊤ := hW.trans_lt ENNReal.one_lt_top
  refine (norm_le_traceW hC hB hc hlt k k' x w w').trans ?_
  have h1 : (traceW c e F).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top hW
    simpa using this
  calc ‖x‖ * ‖w‖ * ‖w'‖ * ((traceW c e F).toReal / Real.sqrt (c k * c k'))
      ≤ ‖x‖ * ‖w‖ * ‖w'‖ * (1 / Real.sqrt (c k * c k')) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h1 (Real.sqrt_nonneg _))
          (by positivity)
    _ = _ := by ring

omit hc in
theorem zero_mem_coneSet : (0 : Coord 𝒜 κ W → ℂ) ∈ coneSet Rel c e := by
  refine ⟨⟨IsConeElement.zero, fun s => by simp⟩, fun k k' x w w' => ?_⟩
  simp only [Pi.zero_apply, norm_zero]
  positivity

/-- A scaled bounded cone element with weighted trace one lies in the compact set. -/
theorem smul_inv_mem_coneSet (hC : IsConeElement Rel F) (hB : IsBoundedForm F)
    (h0 : traceW c e F ≠ 0) (htop : traceW c e F ≠ ⊤) :
    ((traceW c e F).toReal)⁻¹ • F ∈ coneSet Rel c e := by
  have hpos : 0 < (traceW c e F).toReal := ENNReal.toReal_pos h0 htop
  refine mem_coneSet_of hc (hC.smul (inv_nonneg.mpr hpos.le)) (hB.smul _) (le_of_eq ?_)
  rw [traceW_smul (inv_nonneg.mpr hpos.le)]
  calc ENNReal.ofReal ((traceW c e F).toReal)⁻¹ * traceW c e F
      = ENNReal.ofReal ((traceW c e F).toReal)⁻¹ * ENNReal.ofReal (traceW c e F).toReal := by
        rw [ENNReal.ofReal_toReal htop]
    _ = ENNReal.ofReal (((traceW c e F).toReal)⁻¹ * (traceW c e F).toReal) :=
        (ENNReal.ofReal_mul (inv_nonneg.mpr hpos.le)).symm
    _ = 1 := by rw [inv_mul_cancel₀ hpos.ne', ENNReal.ofReal_one]

/-! ### Extreme points -/

theorem traceW_eq_one_of_extreme (hext : F ∈ (coneSet Rel c e).extremePoints ℝ)
    (hne : F ≠ 0) : traceW c e F = 1 := by
  have hmem := hext.1
  have hC := hmem.1.1
  have hB := isBoundedForm_of_mem hmem
  have hle := traceW_le_one_of_mem hc hmem
  have hpos : traceW c e F ≠ 0 := fun h => hne (traceW_zero_imp hC hB hc h)
  by_contra hne1
  have hlt : traceW c e F < 1 := lt_of_le_of_ne hle hne1
  have htop : traceW c e F ≠ ⊤ := (hlt.trans ENNReal.one_lt_top).ne
  set s := (traceW c e F).toReal with hs
  have hs_pos : 0 < s := ENNReal.toReal_pos hpos htop
  have hs_lt : s < 1 := by
    have := ENNReal.toReal_strict_mono ENNReal.one_ne_top hlt
    simpa using this
  have hG := smul_inv_mem_coneSet hc hC hB hpos htop
  have hseg : F ∈ openSegment ℝ 0 (s⁻¹ • F) :=
    ⟨1 - s, s, by linarith, hs_pos, by ring, by
      rw [smul_zero, zero_add, smul_smul, mul_inv_cancel₀ hs_pos.ne', one_smul]⟩
  exact hne (hext.2 zero_mem_coneSet hG hseg).symm

theorem compress_eq_smul_of_extreme (hext : F ∈ (coneSet Rel c e).extremePoints ℝ)
    (hne : F ≠ 0) (hC : IsConeElement Rel F) {Q : Space hC →L[ℂ] Space hC}
    (hQ : IsStarProjection Q) (hQc : ∀ a, Commute Q (rho hC a)) :
    ∃ t : ℝ, compress hC Q = t • F := by
  have hB := isBoundedForm_of_mem hext.1
  have h1 := traceW_eq_one_of_extreme hc hext hne
  have hQ' : IsStarProjection (1 - Q) := hQ.one_sub
  have hQc' : ∀ a, Commute (1 - Q) (rho hC a) := fun a => (Commute.one_left _).sub_left (hQc a)
  have hC₁ := isConeElement_compress hC hQ hQc
  have hC₂ := isConeElement_compress hC hQ' hQc'
  have hB₁ := isBoundedForm_compress hC hB Q
  have hB₂ := isBoundedForm_compress hC hB (1 - Q)
  have hsum : compress hC Q + compress hC (1 - Q) = F := by
    rw [compress_one_sub, add_sub_cancel]
  have htr : traceW c e (compress hC Q) + traceW c e (compress hC (1 - Q)) = 1 := by
    rw [← traceW_add hc hC₁ hC₂, hsum, h1]
  by_cases hz₁ : traceW c e (compress hC Q) = 0
  · exact ⟨0, by rw [traceW_zero_imp hC₁ hB₁ hc hz₁, zero_smul]⟩
  by_cases hz₂ : traceW c e (compress hC (1 - Q)) = 0
  · have h0 := traceW_zero_imp hC₂ hB₂ hc hz₂
    rw [h0, add_zero] at hsum
    exact ⟨1, by rw [one_smul]; exact hsum⟩
  have hle₁ : traceW c e (compress hC Q) ≤ 1 := by rw [← htr]; exact le_self_add
  have hle₂ : traceW c e (compress hC (1 - Q)) ≤ 1 := by rw [← htr]; exact le_add_self
  have ht₁ : traceW c e (compress hC Q) ≠ ⊤ := (hle₁.trans_lt ENNReal.one_lt_top).ne
  have ht₂ : traceW c e (compress hC (1 - Q)) ≠ ⊤ := (hle₂.trans_lt ENNReal.one_lt_top).ne
  set t := (traceW c e (compress hC Q)).toReal with ht
  have ht_pos : 0 < t := ENNReal.toReal_pos hz₁ ht₁
  have h2 : (traceW c e (compress hC (1 - Q))).toReal = 1 - t := by
    have := congrArg ENNReal.toReal htr
    rw [ENNReal.toReal_add ht₁ ht₂, ENNReal.toReal_one] at this
    linarith
  have h2pos : 0 < 1 - t := by rw [← h2]; exact ENNReal.toReal_pos hz₂ ht₂
  have hG₁ := smul_inv_mem_coneSet hc hC₁ hB₁ hz₁ ht₁
  have hG₂ := smul_inv_mem_coneSet hc hC₂ hB₂ hz₂ ht₂
  rw [h2] at hG₂
  rw [← ht] at hG₁
  have hseg : F ∈ openSegment ℝ (t⁻¹ • compress hC Q) ((1 - t)⁻¹ • compress hC (1 - Q)) :=
    ⟨t, 1 - t, ht_pos, h2pos, by ring, by
      rw [smul_smul, smul_smul, mul_inv_cancel₀ ht_pos.ne', mul_inv_cancel₀ h2pos.ne',
        one_smul, one_smul, hsum]⟩
  have heq := hext.2 hG₁ hG₂ hseg
  refine ⟨t, ?_⟩
  calc compress hC Q = t • (t⁻¹ • compress hC Q) := by
        rw [smul_smul, mul_inv_cancel₀ ht_pos.ne', one_smul]
    _ = t • F := by rw [heq]

/-- For strictly positive weights `c` and a nonzero extreme point `F` of `coneSet Rel c e`, an
orthogonal projection commuting with `ρ(𝒜)` is `0` or `1`. -/
theorem eq_zero_or_one_of_extreme (hext : F ∈ (coneSet Rel c e).extremePoints ℝ)
    (hne : F ≠ 0) (hC : IsConeElement Rel F) {Q : Space hC →L[ℂ] Space hC}
    (hQ : IsStarProjection Q) (hQc : ∀ a, Commute Q (rho hC a)) : Q = 0 ∨ Q = 1 := by
  obtain ⟨t, ht⟩ := compress_eq_smul_of_extreme hc hext hne hC hQ hQc
  have hQt : Q = (t : ℂ) • (1 : Space hC →L[ℂ] Space hC) := by
    refine clm_ext hC fun x k w => ext_vec hC fun y k' w' => ?_
    have h := congrFun (congrFun (congrArg kernelOf ht) (x, k, w)) (y, k', w')
    rw [kernelOf_compress hC hQc] at h
    rw [h, smul_apply, one_apply_eq_self, inner_smul_left, inner_vec,
      Complex.conj_ofReal]
    rfl
  have hidem : Q * Q = Q := hQ.isIdempotentElem.eq
  rw [hQt, smul_mul_smul, one_mul] at hidem
  by_cases h1 : (1 : Space hC →L[ℂ] Space hC) = 0
  · left; rw [hQt, h1, smul_zero]
  · have htt : (t : ℂ) * t = t := smul_left_injective ℂ h1 hidem
    have : (t : ℂ) * (t - 1) = 0 := by rw [mul_sub, htt, mul_one, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · left; rw [hQt, h, zero_smul]
    · right; rw [hQt, sub_eq_zero.mp h, one_smul]

end Membership

end Langlands.Analysis.KernelCone
