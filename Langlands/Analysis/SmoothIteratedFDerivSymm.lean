import Mathlib

/-!
# Symmetry and nesting of iterated derivatives of finitely smooth functions

Over `𝕜 = ℝ` or `ℂ` (`RCLike 𝕜`), if `f : E → F` is `C^n` at `x` and `k ≤ n`, then the `k`-th
iterated Fréchet derivative `iteratedFDeriv 𝕜 k f x` is a symmetric multilinear map: permuting
its arguments does not change its value. Mathlib proves this only for analytic functions
(`ContDiffAt.iteratedFDeriv_comp_perm`, smoothness `ω`) and for second derivatives
(`ContDiffAt.isSymmSndFDerivAt`); here it is proved for any finite smoothness, hence also for
`ContDiff 𝕜 ∞` functions.

We also prove the nesting identity
`iteratedFDeriv 𝕜 (j + p) f x (Fin.append m v) =
  iteratedFDeriv 𝕜 j (fun y => iteratedFDeriv 𝕜 p f y v) x m`,
expressed with the ordered iterated line derivative `iteratedLineDeriv 𝕜 p f v`.
-/

namespace Langlands.Analysis

open scoped ContDiff Topology
open Equiv Filter Function Set

universe uE uF

variable (𝕜 : Type*) [RCLike 𝕜] {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The ordered iterated line derivative `∂_{v 0} ⋯ ∂_{v (p - 1)} f` at `x`: the `p`-th iterated
Fréchet derivative of `f` at `x`, evaluated on the word `v`. -/
noncomputable def iteratedLineDeriv {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (p : ℕ) (f : E → F) (v : Fin p → E) (x : E) : F :=
  iteratedFDeriv 𝕜 p f x v

variable {𝕜}

theorem iteratedLineDeriv_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (p : ℕ) (f : E → F) (v : Fin p → E) (x : E) :
    iteratedLineDeriv 𝕜 p f v x = iteratedFDeriv 𝕜 p f x v :=
  rfl

/-- Swapping the last two arguments of an iterated derivative of a function that is `C²` at `x`
(Schwarz's theorem applied at all points near `x`). -/
theorem iteratedFDeriv_comp_swap_last {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {x : E} (hf : ContDiffAt 𝕜 2 f x) {m : ℕ} (v : Fin (m + 2) → E) :
    iteratedFDeriv 𝕜 (m + 2) f x (v ∘ swap (Fin.last m).castSucc (Fin.last (m + 1))) =
      iteratedFDeriv 𝕜 (m + 2) f x v := by
  set G : E → E →L[𝕜] E →L[𝕜] F := fun y => fderiv 𝕜 (fun z => fderiv 𝕜 f z) y with hG
  let e : (E →L[𝕜] E →L[𝕜] F) ≃L[𝕜] (E →L[𝕜] E →L[𝕜] F) :=
    (ContinuousLinearMap.flipₗᵢ 𝕜 E E F).toContinuousLinearEquiv
  have hsymm : G =ᶠ[𝓝 x] e ∘ G := by
    filter_upwards [hf.eventually (by simp)] with y hy
    ext a b
    exact (hy.isSymmSndFDerivAt (by simp)) a b
  have key : ∀ (u : Fin m → E) (a b : E),
      iteratedFDeriv 𝕜 m G x u a b = iteratedFDeriv 𝕜 m G x u b a := by
    intro u a b
    have h1 : iteratedFDeriv 𝕜 m G x = iteratedFDeriv 𝕜 m (e ∘ G) x :=
      (hsymm.iteratedFDeriv 𝕜 m).eq_of_nhds
    have h3 := ContinuousLinearEquiv.iteratedFDeriv_comp_left (𝕜 := 𝕜)
      (F := E →L[𝕜] E →L[𝕜] F) (G := E →L[𝕜] E →L[𝕜] F) (f := G) (x := x) (i := m) e
    calc iteratedFDeriv 𝕜 m G x u a b = iteratedFDeriv 𝕜 m (e ∘ G) x u a b := by rw [h1]
      _ = iteratedFDeriv 𝕜 m G x u b a := by rw [h3]; rfl
  have h2 : ∀ w : Fin (m + 2) → E, iteratedFDeriv 𝕜 (m + 2) f x w =
      iteratedFDeriv 𝕜 m G x (Fin.init (Fin.init w)) (w (Fin.last m).castSucc)
        (w (Fin.last (m + 1))) := by
    intro w
    rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_succ_apply_right]
    rfl
  rw [h2, h2]
  have hinit : Fin.init (Fin.init (v ∘ swap (Fin.last m).castSucc (Fin.last (m + 1)))) =
      Fin.init (Fin.init v) := by
    funext i
    simp only [Fin.init, comp_apply]
    rw [swap_apply_of_ne_of_ne]
    · exact fun h => Fin.castSucc_ne_last i (Fin.castSucc_inj.1 h)
    · exact Fin.castSucc_ne_last _
  rw [hinit]
  simp only [comp_apply, swap_apply_left, swap_apply_right]
  exact key _ _ _

/-- Extension of a permutation of `Fin k` to `Fin (k + 1)` fixing the last element. -/
private def permExtendLast {k : ℕ} (τ : Perm (Fin k)) : Perm (Fin (k + 1)) :=
  finSuccEquivLast.symm.permCongr (optionCongr τ)

private theorem permExtendLast_castSucc {k : ℕ} (τ : Perm (Fin k)) (i : Fin k) :
    permExtendLast τ i.castSucc = (τ i).castSucc := by
  simp [permExtendLast, permCongr_apply, finSuccEquivLast_castSucc, finSuccEquivLast_symm_some]

private theorem permExtendLast_last {k : ℕ} (τ : Perm (Fin k)) :
    permExtendLast τ (Fin.last k) = Fin.last k := by
  simp [permExtendLast, permCongr_apply, finSuccEquivLast_last]

private theorem permExtendLast_swap {k : ℕ} (a b : Fin k) :
    permExtendLast (swap a b) = swap a.castSucc b.castSucc := by
  ext t
  induction t using Fin.lastCases with
  | last =>
    rw [permExtendLast_last, swap_apply_of_ne_of_ne (Fin.castSucc_ne_last a).symm
      (Fin.castSucc_ne_last b).symm]
  | cast i =>
    rw [permExtendLast_castSucc, (Fin.castSucc_injective k).swap_apply]

/-- Symmetry of iterated derivatives, for codomains in the universe `max uE uF`; the induction
passes from `f` to `fderiv 𝕜 f`, whose codomain `E →L[𝕜] F` stays in that universe. -/
private theorem iteratedFDeriv_comp_perm_aux : ∀ (k : ℕ) {F : Type (max uE uF)}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {x : E}, ContDiffAt 𝕜 k f x →
    ∀ (v : Fin k → E) (σ : Perm (Fin k)),
      iteratedFDeriv 𝕜 k f x (v ∘ σ) = iteratedFDeriv 𝕜 k f x v
  | 0, F, _, _, f, x, _, v, σ => by
    congr 1
    exact Subsingleton.elim _ _
  | k + 1, F, _, _, f, x, hf, v, σ => by
    have hf' : ContDiffAt 𝕜 k (fun y => fderiv 𝕜 f y) x :=
      hf.fderiv_right (by push_cast; exact le_rfl)
    -- the permutations under which the derivative at `x` is invariant
    let S : Submonoid (Perm (Fin (k + 1))) :=
      { carrier := {σ | ∀ w : Fin (k + 1) → E,
          iteratedFDeriv 𝕜 (k + 1) f x (w ∘ σ) = iteratedFDeriv 𝕜 (k + 1) f x w}
        mul_mem' := by
          intro σ τ hσ hτ w
          rw [Perm.coe_mul, ← comp_assoc]
          exact (hτ (w ∘ σ)).trans (hσ w)
        one_mem' := fun w => rfl }
    have hext : ∀ τ : Perm (Fin k), permExtendLast τ ∈ S := by
      intro τ w
      rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_succ_apply_right]
      have hinit : Fin.init (w ∘ permExtendLast τ) = Fin.init w ∘ τ := by
        funext i
        simp [Fin.init, permExtendLast_castSucc]
      rw [hinit, comp_apply, permExtendLast_last,
        iteratedFDeriv_comp_perm_aux k hf' (Fin.init w) τ]
    have hswap : ∀ i : Fin k, swap i.castSucc i.succ ∈ S := by
      intro i
      cases k with
      | zero => exact i.elim0
      | succ k =>
        induction i using Fin.lastCases with
        | last =>
          intro w
          rw [Fin.succ_last]
          exact iteratedFDeriv_comp_swap_last (hf.of_le (by exact_mod_cast (show 2 ≤ k + 1 + 1 by omega))) w
        | cast j =>
          rw [Fin.succ_castSucc, ← permExtendLast_swap]
          exact hext _
    have hS : S = ⊤ := by
      rw [eq_top_iff, ← Perm.mclosure_swap_castSucc_succ k, Submonoid.closure_le]
      rintro _ ⟨i, rfl⟩
      exact hswap i
    have hσ : σ ∈ S := hS ▸ Submonoid.mem_top σ
    exact hσ v

/-- **Symmetry of iterated derivatives.** If `f` is `C^n` at `x` and `k ≤ n`, then
`iteratedFDeriv 𝕜 k f x` is invariant under every permutation of its arguments. -/
theorem iteratedFDeriv_comp_perm_of_contDiffAt {F : Type uF} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {n : WithTop ℕ∞} {f : E → F} {x : E} (hf : ContDiffAt 𝕜 n f x) {k : ℕ}
    (hk : (k : WithTop ℕ∞) ≤ n) (v : Fin k → E) (σ : Perm (Fin k)) :
    iteratedFDeriv 𝕜 k f x (v ∘ σ) = iteratedFDeriv 𝕜 k f x v := by
  let e : ULift.{uE} F ≃L[𝕜] F := ContinuousLinearEquiv.ulift
  have hg : ContDiffAt 𝕜 k (e.symm ∘ f) x := e.symm.comp_contDiffAt_iff.2 (hf.of_le hk)
  have h := iteratedFDeriv_comp_perm_aux.{uE, uF} k hg v σ
  rw [e.symm.iteratedFDeriv_comp_left] at h
  exact e.symm.injective h

/-- Symmetry of iterated derivatives at points of an open set on which `f` is `C^n`. -/
theorem iteratedFDeriv_comp_perm_of_contDiffOn {F : Type uF} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {n : WithTop ℕ∞} {f : E → F} {s : Set E} (hf : ContDiffOn 𝕜 n f s)
    (hs : IsOpen s) {x : E} (hx : x ∈ s) {k : ℕ} (hk : (k : WithTop ℕ∞) ≤ n) (v : Fin k → E)
    (σ : Perm (Fin k)) :
    iteratedFDeriv 𝕜 k f x (v ∘ σ) = iteratedFDeriv 𝕜 k f x v :=
  iteratedFDeriv_comp_perm_of_contDiffAt (hf.contDiffAt (hs.mem_nhds hx)) hk v σ

/-- Symmetry of iterated derivatives under a bijection between index types `Fin k ≃ Fin l`
(so `k = l`). -/
theorem iteratedFDeriv_comp_equiv_of_contDiffAt {F : Type uF} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {n : WithTop ℕ∞} {f : E → F} {x : E} (hf : ContDiffAt 𝕜 n f x) {k l : ℕ}
    (hl : (l : WithTop ℕ∞) ≤ n) (e : Fin k ≃ Fin l) (v : Fin l → E) :
    iteratedFDeriv 𝕜 k f x (v ∘ e) = iteratedFDeriv 𝕜 l f x v := by
  obtain rfl : k = l := by simpa using Fintype.card_congr e
  exact iteratedFDeriv_comp_perm_of_contDiffAt hf hl v e

/-- Nesting identity for codomains in the universe `max uE uF`, by induction on the inner
order `p`. -/
private theorem iteratedFDeriv_append_aux (j : ℕ) : ∀ (p : ℕ) {F : Type (max uE uF)}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {x : E},
    ContDiffAt 𝕜 (j + p : ℕ) f x → ∀ (m : Fin j → E) (v : Fin p → E),
      iteratedFDeriv 𝕜 (j + p) f x (Fin.append m v) =
        iteratedFDeriv 𝕜 j (fun y => iteratedFDeriv 𝕜 p f y v) x m
  | 0, F, _, _, f, x, _, m, v => by
    simp only [iteratedFDeriv_zero_apply]
    exact congrArg (iteratedFDeriv 𝕜 j f x) (funext fun i => Fin.append_left m v i)
  | p + 1, F, _, _, f, x, hf, m, v => by
    have hf' : ContDiffAt 𝕜 (j + p : ℕ) (fun y => fderiv 𝕜 f y) x :=
      hf.fderiv_right (by push_cast; exact le_rfl)
    have IH := iteratedFDeriv_append_aux j p hf' m (Fin.init v)
    have hD : ContDiffAt 𝕜 j (iteratedFDeriv 𝕜 p (fun y => fderiv 𝕜 f y)) x :=
      hf'.iteratedFDeriv_right (by push_cast; exact le_rfl)
    have hG : ContDiffAt 𝕜 j (fun y => iteratedFDeriv 𝕜 p (fun y => fderiv 𝕜 f y) y (Fin.init v))
        x :=
      ContDiffAt.congr_of_eventuallyEq
        ((ContinuousMultilinearMap.apply 𝕜 (fun _ : Fin p => E) (E →L[𝕜] F)
          (Fin.init v)).contDiff.contDiffAt.comp x hD) (Eventually.of_forall fun _ => rfl)
    have hfun : (fun y => iteratedFDeriv 𝕜 (p + 1) f y v) =
        ContinuousLinearMap.apply 𝕜 F (v (Fin.last p)) ∘
          (fun y => iteratedFDeriv 𝕜 p (fun y => fderiv 𝕜 f y) y (Fin.init v)) := by
      funext y
      rw [iteratedFDeriv_succ_apply_right]
      rfl
    have happ : Fin.append m v = Fin.snoc (Fin.append m (Fin.init v)) (v (Fin.last p)) := by
      rw [← Fin.append_snoc, Fin.snoc_init_self]
    calc iteratedFDeriv 𝕜 (j + (p + 1)) f x (Fin.append m v)
        = iteratedFDeriv 𝕜 (j + p) (fun y => fderiv 𝕜 f y) x (Fin.append m (Fin.init v))
            (v (Fin.last p)) := by
          rw [happ]
          exact (iteratedFDeriv_succ_apply_right (n := j + p) _).trans
            (by rw [Fin.init_snoc]; exact congrArg _ (Fin.snoc_last (α := fun _ => E) _ _))
      _ = iteratedFDeriv 𝕜 j (fun y => iteratedFDeriv 𝕜 p (fun y => fderiv 𝕜 f y) y
            (Fin.init v)) x m (v (Fin.last p)) := by rw [IH]
      _ = iteratedFDeriv 𝕜 j (fun y => iteratedFDeriv 𝕜 (p + 1) f y v) x m := by
          rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_left _ hG le_rfl]
          rfl

/-- **Nesting identity.** If `f` is `C^n` at `x` and `j + p ≤ n`, then the `j`-th derivative at
`x` of the line derivative `y ↦ iteratedFDeriv 𝕜 p f y v`, evaluated on `m`, is the
`(j + p)`-th derivative of `f` at `x` evaluated on the concatenated word `Fin.append m v`. -/
theorem iteratedFDeriv_append_of_contDiffAt {F : Type uF} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {n : WithTop ℕ∞} {f : E → F} {x : E} (hf : ContDiffAt 𝕜 n f x) {j p : ℕ}
    (hjp : ((j + p : ℕ) : WithTop ℕ∞) ≤ n) (m : Fin j → E) (v : Fin p → E) :
    iteratedFDeriv 𝕜 (j + p) f x (Fin.append m v) =
      iteratedFDeriv 𝕜 j (fun y => iteratedFDeriv 𝕜 p f y v) x m := by
  let e : ULift.{uE} F ≃L[𝕜] F := ContinuousLinearEquiv.ulift
  have hg : ContDiffAt 𝕜 (j + p : ℕ) (e.symm ∘ f) x := e.symm.comp_contDiffAt_iff.2 (hf.of_le hjp)
  have h := iteratedFDeriv_append_aux.{uE, uF} j p hg m v
  have hfun : (fun y => iteratedFDeriv 𝕜 p (e.symm ∘ f) y v) =
      e.symm ∘ (fun y => iteratedFDeriv 𝕜 p f y v) := by
    funext y
    rw [e.symm.iteratedFDeriv_comp_left]
    rfl
  rw [hfun, e.symm.iteratedFDeriv_comp_left, e.symm.iteratedFDeriv_comp_left] at h
  exact e.symm.injective h

/-- The nesting identity at points of an open set on which `f` is `C^n`. -/
theorem iteratedFDeriv_append_of_contDiffOn {F : Type uF} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {n : WithTop ℕ∞} {f : E → F} {s : Set E} (hf : ContDiffOn 𝕜 n f s)
    (hs : IsOpen s) {x : E} (hx : x ∈ s) {j p : ℕ} (hjp : ((j + p : ℕ) : WithTop ℕ∞) ≤ n)
    (m : Fin j → E) (v : Fin p → E) :
    iteratedFDeriv 𝕜 (j + p) f x (Fin.append m v) =
      iteratedFDeriv 𝕜 j (fun y => iteratedFDeriv 𝕜 p f y v) x m :=
  iteratedFDeriv_append_of_contDiffAt (hf.contDiffAt (hs.mem_nhds hx)) hjp m v

theorem append_comp_finAddFlip {α : Type*} {j p : ℕ} (m : Fin j → α) (v : Fin p → α) :
    Fin.append v m ∘ finAddFlip = Fin.append m v := by
  funext i
  induction i using Fin.addCases with
  | left i => simp [finAddFlip_apply_castAdd]
  | right i => simp [finAddFlip_apply_natAdd]

/-- The two concatenation orders give the same value of a symmetric iterated derivative. -/
theorem iteratedFDeriv_append_comm_of_contDiffAt {F : Type uF} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {n : WithTop ℕ∞} {f : E → F} {x : E} (hf : ContDiffAt 𝕜 n f x) {j p : ℕ}
    (hjp : ((j + p : ℕ) : WithTop ℕ∞) ≤ n) (m : Fin j → E) (v : Fin p → E) :
    iteratedFDeriv 𝕜 (j + p) f x (Fin.append m v) =
      iteratedFDeriv 𝕜 (p + j) f x (Fin.append v m) := by
  rw [← append_comp_finAddFlip m v]
  exact iteratedFDeriv_comp_equiv_of_contDiffAt hf (by rwa [Nat.add_comm]) _ _

/-- Line derivatives of a function that is `C^n` on an open set are `C^m` there when
`m + p ≤ n`. -/
theorem contDiffOn_iteratedLineDeriv {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {n m : WithTop ℕ∞} {f : E → F} {s : Set E} (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s)
    {p : ℕ} (hmp : m + p ≤ n) (v : Fin p → E) :
    ContDiffOn 𝕜 m (iteratedLineDeriv 𝕜 p f v) s := by
  intro y hy
  have hD : ContDiffAt 𝕜 m (iteratedFDeriv 𝕜 p f) y :=
    (hf.contDiffAt (hs.mem_nhds hy)).iteratedFDeriv_right hmp
  exact ((ContinuousMultilinearMap.apply 𝕜 (fun _ : Fin p => E) F v).contDiff.contDiffAt.comp y
    hD).contDiffWithinAt

/-- Line derivatives of a function that is smooth on an open set are smooth there. -/
theorem contDiffOn_infty_iteratedLineDeriv {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {s : Set E} (hf : ContDiffOn 𝕜 ∞ f s) (hs : IsOpen s) {p : ℕ} (v : Fin p → E) :
    ContDiffOn 𝕜 ∞ (iteratedLineDeriv 𝕜 p f v) s :=
  contDiffOn_iteratedLineDeriv hf hs (by simp) v

/-- Nesting of line derivatives: on an open set where `f` is `C^n` with `j + p ≤ n`, the
line derivative along `m` of the line derivative along `v` is the line derivative along the
concatenated word `Fin.append m v`. -/
theorem iteratedLineDeriv_iteratedLineDeriv {F : Type uF} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {n : WithTop ℕ∞} {f : E → F} {s : Set E} (hf : ContDiffOn 𝕜 n f s)
    (hs : IsOpen s) {x : E} (hx : x ∈ s) {j p : ℕ} (hjp : ((j + p : ℕ) : WithTop ℕ∞) ≤ n)
    (m : Fin j → E) (v : Fin p → E) :
    iteratedLineDeriv 𝕜 j (iteratedLineDeriv 𝕜 p f v) m x =
      iteratedLineDeriv 𝕜 (j + p) f (Fin.append m v) x :=
  (iteratedFDeriv_append_of_contDiffOn hf hs hx hjp m v).symm

/-- Line derivatives along words differing by a permutation agree at points of an open set
where `f` is `C^n` with `k ≤ n`. -/
theorem iteratedLineDeriv_comp_perm {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {n : WithTop ℕ∞} {f : E → F} {s : Set E} (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s) {x : E}
    (hx : x ∈ s) {k : ℕ} (hk : (k : WithTop ℕ∞) ≤ n) (v : Fin k → E) (σ : Perm (Fin k)) :
    iteratedLineDeriv 𝕜 k f (v ∘ σ) x = iteratedLineDeriv 𝕜 k f v x :=
  iteratedFDeriv_comp_perm_of_contDiffOn hf hs hx hk v σ

end Langlands.Analysis
