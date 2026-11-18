import Langlands.Representation.Archimedean.HilbertSmoothKernelStatement
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # Proof of the Hilbert smooth-kernel criterion -/

noncomputable section
set_option autoImplicit false

open Filter Set
open scoped ContDiff Manifold Topology

namespace Langlands.Archimedean

private theorem exists_slope_eq_of_hasDerivAt {g g' : ℝ → ℝ} {t : ℝ} (ht : t ≠ 0)
    (hg : ∀ a ∈ uIcc 0 t, HasDerivAt g (g' a) a) :
    ∃ a ∈ uIcc 0 t, slope g 0 t = g' a := by
  have ordered {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ uIcc 0 t) :
      ∃ c ∈ uIcc 0 t, slope g a b = g' c := by
    obtain ⟨c, hc, heq⟩ := exists_deriv_eq_slope' g hab
      (fun z hz => (hg z (hsub hz)).continuousAt.continuousWithinAt)
      (fun z hz => (hg z (hsub (Ioo_subset_Icc_self hz))).differentiableAt.differentiableWithinAt)
    exact ⟨c, hsub (Ioo_subset_Icc_self hc), heq.symm.trans (hg c (hsub (Ioo_subset_Icc_self hc))).deriv⟩
  rcases lt_or_gt_of_ne ht with h | h
  · simpa only [slope_comm g t 0] using ordered h Icc_subset_uIcc'
  · exact ordered h Icc_subset_uIcc

/-- Two applications of the real scalar mean value theorem on a rectangle. -/
private theorem exists_mixed_eq_rectangularSlope {K K₁ K₁₂ : ℝ → ℝ → ℝ} {t s : ℝ}
    (ht : t ≠ 0) (hs : s ≠ 0)
    (h₁ : ∀ a ∈ uIcc 0 t, ∀ b ∈ uIcc 0 s, HasDerivAt (fun a => K a b) (K₁ a b) a)
    (h₂ : ∀ a ∈ uIcc 0 t, ∀ b ∈ uIcc 0 s, HasDerivAt (K₁ a) (K₁₂ a b) b) :
    ∃ a ∈ uIcc 0 t, ∃ b ∈ uIcc 0 s,
      slope (fun a => slope (K a) 0 s) 0 t = K₁₂ a b := by
  have h (a : ℝ) (ha : a ∈ uIcc 0 t) :
      HasDerivAt (fun a => slope (K a) 0 s) (slope (K₁ a) 0 s) a := by
    simpa only [slope_def_field, sub_zero, Pi.sub_apply] using
      ((h₁ a ha s right_mem_uIcc).sub (h₁ a ha 0 left_mem_uIcc)).div_const s
  obtain ⟨a, ha, hfa⟩ := exists_slope_eq_of_hasDerivAt ht h
  obtain ⟨b, hb, hfb⟩ := exists_slope_eq_of_hasDerivAt hs (h₂ a ha)
  exact ⟨a, ha, b, hb, hfa.trans hfb⟩

private theorem hasDerivAt_affineLine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x v : E) (a : ℝ) : HasDerivAt (fun t : ℝ => x + t • v) v a :=
  (((hasDerivAt_id' a).smul_const v).const_add x).congr_deriv (one_smul ℝ v)

section ModelSpace

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private def realKernel {X : Type*} (f : X → H) (p : X × X) : ℝ :=
  inner ℝ (f p.1) (f p.2)

private def lineQuotient (f : E → H) (x v : E) (t : ℝ) : H :=
  t⁻¹ • (f (x + t • v) - f x)

private def mixedDerivative (K : E × E → ℝ) (v w : E) (p : E × E) : ℝ :=
  fderiv ℝ (fderiv ℝ K) p (0, w) (v, 0)

private theorem contDiffOn_mixedDerivative {U : Set E} (hU : IsOpen U) {K : E × E → ℝ}
    (hK : ContDiffOn ℝ ∞ K (U ×ˢ U)) (v w : E) :
    ContDiffOn ℝ ∞ (mixedDerivative K v w) (U ×ˢ U) := by
  have hprod := hU.prod hU
  have h₂ := (hK.fderiv_of_isOpen (m := ∞) hprod (by simp)).fderiv_of_isOpen
    (m := ∞) hprod (by simp)
  exact (h₂.clm_apply contDiffOn_const).clm_apply contDiffOn_const

/-- The inner products of independently scaled line difference quotients converge jointly. -/
private theorem tendsto_inner_lineQuotient {U : Set E} (hU : IsOpen U) {f : E → H}
    (hK : ContDiffOn ℝ ∞ (realKernel f) (U ×ˢ U)) {x y : E} (hx : x ∈ U) (hy : y ∈ U)
    (v w : E) :
    Tendsto (fun p : ℝ × ℝ => inner ℝ (lineQuotient f x v p.1) (lineQuotient f y w p.2))
      (𝓝[≠] (0 : ℝ) ×ˢ 𝓝[≠] (0 : ℝ)) (𝓝 (mixedDerivative (realKernel f) v w (x, y))) := by
  let P : ℝ × ℝ → E × E := fun p => (x + p.1 • v, y + p.2 • w)
  have hP : Continuous P := by dsimp [P]; fun_prop
  have hP0 : P (0, 0) = (x, y) := by simp [P]
  have hU₀ : ∀ᶠ p in 𝓝 ((0, 0) : ℝ × ℝ), P p ∈ U ×ˢ U :=
    hP.continuousAt.eventually (hP0 ▸ (hU.prod hU).mem_nhds (mk_mem_prod hx hy))
  have hMixed : ContinuousAt (mixedDerivative (realKernel f) v w ∘ P) (0, 0) :=
    ((contDiffOn_mixedDerivative hU hK v w).continuousOn.continuousAt
      (hP0 ▸ (hU.prod hU).mem_nhds (mk_mem_prod hx hy))).comp hP.continuousAt
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hClose : ∀ᶠ p in 𝓝 ((0, 0) : ℝ × ℝ),
      dist (mixedDerivative (realKernel f) v w (P p))
        (mixedDerivative (realKernel f) v w (x, y)) < ε := by
    simpa only [Function.comp_apply, hP0] using (Metric.tendsto_nhds.mp hMixed ε hε)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hU₀.and hClose)
  have hNearby : ∀ᶠ p in (𝓝[≠] (0 : ℝ) ×ˢ 𝓝[≠] (0 : ℝ)), p ∈ Metric.ball (0, 0) δ := by
    apply Filter.Eventually.filter_mono _ (Metric.ball_mem_nhds (0, 0) hδ)
    rw [nhds_prod_eq]
    exact Filter.prod_mono nhdsWithin_le_nhds nhdsWithin_le_nhds
  have hne₁ : ∀ᶠ p in (𝓝[≠] (0 : ℝ) ×ˢ 𝓝[≠] (0 : ℝ)), p.1 ≠ 0 :=
    tendsto_fst.eventually self_mem_nhdsWithin
  have hne₂ : ∀ᶠ p in (𝓝[≠] (0 : ℝ) ×ˢ 𝓝[≠] (0 : ℝ)), p.2 ≠ 0 :=
    tendsto_snd.eventually self_mem_nhdsWithin
  filter_upwards [hNearby, hne₁, hne₂] with p hp hne₁ hne₂
  have hrect (a : ℝ) (ha : a ∈ uIcc 0 p.1) (b : ℝ) (hb : b ∈ uIcc 0 p.2) :
      (a, b) ∈ Metric.ball ((0, 0) : ℝ × ℝ) δ := by
    simp only [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hp ⊢
    have ha' : dist a 0 ≤ dist p.1 0 := by
      simpa only [dist_comm (0 : ℝ) a, dist_comm (0 : ℝ) p.1] using
        Real.dist_left_le_of_mem_uIcc ha
    have hb' : dist b 0 ≤ dist p.2 0 := by
      simpa only [dist_comm (0 : ℝ) b, dist_comm (0 : ℝ) p.2] using
        Real.dist_left_le_of_mem_uIcc hb
    exact ⟨ha'.trans_lt hp.1, hb'.trans_lt hp.2⟩
  have hAt (a : ℝ) (ha : a ∈ uIcc 0 p.1) (b : ℝ) (hb : b ∈ uIcc 0 p.2) :
      ContDiffAt ℝ ∞ (realKernel f) (P (a, b)) :=
    hK.contDiffAt ((hU.prod hU).mem_nhds (hball (hrect a ha b hb)).1)
  let K : ℝ → ℝ → ℝ := fun a b => realKernel f (P (a, b))
  let K₁ : ℝ → ℝ → ℝ := fun a b => fderiv ℝ (realKernel f) (P (a, b)) (v, 0)
  have h₁ (a : ℝ) (ha : a ∈ uIcc 0 p.1) (b : ℝ) (hb : b ∈ uIcc 0 p.2) :
      HasDerivAt (fun a => K a b) (K₁ a b) a := by
    exact ((hAt a ha b hb).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt a
      ((hasDerivAt_affineLine x v a).prodMk (hasDerivAt_const a (y + b • w)))
  have h₂ (a : ℝ) (ha : a ∈ uIcc 0 p.1) (b : ℝ) (hb : b ∈ uIcc 0 p.2) :
      HasDerivAt (K₁ a) (mixedDerivative (realKernel f) v w (P (a, b))) b := by
    have hD := ((hAt a ha b hb).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
    have hLine := hD.hasFDerivAt.comp_hasDerivAt b
      ((hasDerivAt_const b (x + a • v)).prodMk (hasDerivAt_affineLine y w b))
    simpa only [K₁, mixedDerivative, Function.comp_def, ContinuousLinearMap.map_zero, add_zero]
      using hLine.clm_apply (hasDerivAt_const b (v, (0 : E)))
  obtain ⟨a, ha, b, hb, heq⟩ := exists_mixed_eq_rectangularSlope hne₁ hne₂ h₁ h₂
  have hInner : inner ℝ (lineQuotient f x v p.1) (lineQuotient f y w p.2) =
      slope (fun a => slope (K a) 0 p.2) 0 p.1 := by
    simp only [lineQuotient, real_inner_smul_left, real_inner_smul_right, inner_sub_left,
      inner_sub_right, slope_def_field, K, realKernel, P, zero_smul, add_zero, sub_zero, div_eq_mul_inv]
    ring
  rw [hInner, heq]
  exact (hball (hrect a ha b hb)).2

/-- Continuity and the Cauchy argument both use the same squared-distance identity. -/
private theorem tendsto_dist_zero_of_inner {X : Type*} {l : Filter X} {f g : X → H} {a : ℝ}
    (hff : Tendsto (fun t => inner ℝ (f t) (f t)) l (𝓝 a))
    (hfg : Tendsto (fun t => inner ℝ (f t) (g t)) l (𝓝 a))
    (hgg : Tendsto (fun t => inner ℝ (g t) (g t)) l (𝓝 a)) :
    Tendsto (fun t => dist (f t) (g t)) l (𝓝 0) := by
  have h := (hff.sub (tendsto_const_nhds.mul hfg : Tendsto
    (fun t => 2 * inner ℝ (f t) (g t)) l (𝓝 (2 * a)))).add hgg
  have hzero : a - 2 * a + a = 0 := by ring
  rw [hzero] at h
  simpa only [Function.comp_def, Real.sqrt_zero, real_inner_self_eq_norm_sq,
    ← norm_sub_sq_real, Real.sqrt_sq_eq_abs, abs_norm, dist_eq_norm]
    using (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h

private theorem continuousOn_of_continuousOn_realKernel {X : Type*} [TopologicalSpace X]
    {U : Set X} (hU : IsOpen U) {f : X → H}
    (hK : ContinuousOn (realKernel f) (U ×ˢ U)) : ContinuousOn f U := by
  intro x hx
  have h : ContinuousAt (realKernel f) (x, x) :=
    hK.continuousAt ((hU.prod hU).mem_nhds (mk_mem_prod hx hx))
  apply ContinuousAt.continuousWithinAt
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact tendsto_dist_zero_of_inner
    (h.tendsto.comp (tendsto_id.prodMk_nhds tendsto_id))
    (h.tendsto.comp (tendsto_id.prodMk_nhds tendsto_const_nhds))
    tendsto_const_nhds

variable [CompleteSpace H]

private theorem hasLineDerivAt_of_smoothKernel {U : Set E} (hU : IsOpen U) {f : E → H}
    (hK : ContDiffOn ℝ ∞ (realKernel f) (U ×ˢ U)) {x : E} (hx : x ∈ U) (v : E) :
    HasLineDerivAt ℝ f (lineDeriv ℝ f x v) x v := by
  have hInner := tendsto_inner_lineQuotient hU hK hx hx v v
  have hCauchy : Cauchy ((𝓝[≠] (0 : ℝ)).map (lineQuotient f x v)) := by
    rw [cauchy_map_iff', tendsto_uniformity_iff_dist_tendsto_zero]
    exact tendsto_dist_zero_of_inner
      (hInner.comp (tendsto_fst.prodMk tendsto_fst)) hInner
      (hInner.comp (tendsto_snd.prodMk tendsto_snd))
  obtain ⟨d, hd⟩ := cauchy_map_iff_exists_tendsto.mp hCauchy
  have h := hasLineDerivAt_iff_tendsto_slope_zero.mpr hd
  rw [h.lineDeriv]
  exact h

private theorem inner_lineDeriv_of_smoothKernel {U : Set E} (hU : IsOpen U) {f : E → H}
    (hK : ContDiffOn ℝ ∞ (realKernel f) (U ×ˢ U)) {x y : E} (hx : x ∈ U) (hy : y ∈ U)
    (v w : E) :
    inner ℝ (lineDeriv ℝ f x v) (lineDeriv ℝ f y w) = mixedDerivative (realKernel f) v w (x, y) :=
  tendsto_nhds_unique
    (((hasLineDerivAt_of_smoothKernel hU hK hx v).tendsto_slope_zero.comp tendsto_fst).inner
      (𝕜 := ℝ) ((hasLineDerivAt_of_smoothKernel hU hK hy w).tendsto_slope_zero.comp tendsto_snd))
    (tendsto_inner_lineQuotient hU hK hx hy v w)

private theorem contDiffOn_realKernel_lineDeriv {U : Set E} (hU : IsOpen U) {f : E → H}
    (hK : ContDiffOn ℝ ∞ (realKernel f) (U ×ˢ U)) (v : E) :
    ContDiffOn ℝ ∞ (realKernel (fun x => lineDeriv ℝ f x v)) (U ×ˢ U) :=
  (contDiffOn_mixedDerivative hU hK v v).congr fun _ hp =>
    inner_lineDeriv_of_smoothKernel hU hK hp.1 hp.2 v v

private theorem lineDeriv_add_of_smoothKernel {U : Set E} (hU : IsOpen U) {f : E → H}
    (hK : ContDiffOn ℝ ∞ (realKernel f) (U ×ˢ U)) {x : E} (hx : x ∈ U) (v w : E) :
    lineDeriv ℝ f x (v + w) = lineDeriv ℝ f x v + lineDeriv ℝ f x w := by
  let d := lineDeriv ℝ f x
  let e := d (v + w) - (d v + d w)
  have h (z : E) : inner ℝ e (d z) = 0 := by
    have hpair : ((v + w, 0) : E × E) = (v, 0) + (w, 0) := by simp
    simp only [e, d, inner_sub_left, inner_add_left,
      inner_lineDeriv_of_smoothKernel hU hK hx hx, mixedDerivative, hpair, map_add, sub_self]
  have hSelf : inner ℝ e e = 0 := by
    change inner ℝ e (d (v + w) - (d v + d w)) = 0
    simp only [inner_sub_right, inner_add_right, h, add_zero, sub_zero]
  exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℝ)).mp hSelf)

variable [FiniteDimensional ℝ E]

/-- The directional derivative packaged as a real continuous linear map on the open domain. -/
private def kernelFDeriv {U : Set E} (hU : IsOpen U) {f : E → H}
    (hK : ContDiffOn ℝ ∞ (realKernel f) (U ×ˢ U)) (x : E) : E →L[ℝ] H := by
  classical
  exact if hx : x ∈ U then
    LinearMap.toContinuousLinearMap
      { toFun := lineDeriv ℝ f x
        map_add' := lineDeriv_add_of_smoothKernel hU hK hx
        map_smul' := fun c v => ((hasLineDerivAt_of_smoothKernel hU hK hx v).smul c).lineDeriv }
  else 0

private theorem kernelFDeriv_apply {U : Set E} (hU : IsOpen U) {f : E → H}
    (hK : ContDiffOn ℝ ∞ (realKernel f) (U ×ˢ U)) {x : E} (hx : x ∈ U) (v : E) :
    kernelFDeriv hU hK x v = lineDeriv ℝ f x v := by
  simp only [kernelFDeriv, dite_eq_left hx, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk]

private theorem continuousOn_kernelFDeriv {U : Set E} (hU : IsOpen U) {f : E → H}
    (hK : ContDiffOn ℝ ∞ (realKernel f) (U ×ˢ U)) : ContinuousOn (kernelFDeriv hU hK) U := by
  rw [← contDiffOn_zero (𝕜 := ℝ), contDiffOn_clm_apply]
  intro v
  exact contDiffOn_zero.mpr ((continuousOn_of_continuousOn_realKernel hU
    (contDiffOn_realKernel_lineDeriv hU hK v).continuousOn).congr
      (fun _ hx => kernelFDeriv_apply hU hK hx v))

omit [CompleteSpace H] [FiniteDimensional ℝ E] in
private theorem hasDerivAt_line_of_hasLineDerivAt {f : E → H} {x v : E} {a : ℝ} {d : H}
    (h : HasLineDerivAt ℝ f d (x + a • v) v) :
    HasDerivAt (fun t : ℝ => f (x + t • v)) d a := by
  have h' : HasDerivAt (fun t : ℝ => f ((x + a • v) + t • v)) d (a - a) := by
    simpa only [sub_self, HasLineDerivAt] using h
  convert h'.comp_sub_const a a using 1
  ext t
  rw [add_assoc, ← add_smul, add_comm a, sub_add_cancel]

private theorem hasFDerivAt_of_smoothKernel {U : Set E} (hU : IsOpen U) {f : E → H}
    (hK : ContDiffOn ℝ ∞ (realKernel f) (U ×ˢ U)) {x : E} (hx : x ∈ U) :
    HasFDerivAt f (kernelFDeriv hU hK x) x := by
  let D := kernelFDeriv hU hK
  have hD : ContinuousAt D x := (continuousOn_kernelFDeriv hU hK).continuousAt (hU.mem_nhds hx)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  have hUn : ∀ᶠ y in 𝓝 x, y ∈ U := hU.mem_nhds hx
  have hNear : ∀ᶠ y in 𝓝 x, y ∈ U ∧ dist (D y) (D x) < ε :=
    hUn.and (hD.eventually (Metric.ball_mem_nhds (D x) hε))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hNear
  filter_upwards [Metric.ball_mem_nhds (0 : E) hδ] with h hh
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : x + t • h ∈ U ∧ dist (D (x + t • h)) (D x) < ε := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have ht' : |t| ≤ 1 := (abs_of_nonneg ht.1).trans_le ht.2
    exact (mul_le_of_le_one_left (norm_nonneg h) ht').trans_lt
      (by simpa only [Metric.mem_ball, dist_zero_right] using hh)
  let g (t : ℝ) := f (x + t • h) - t • D x h
  let g' (t : ℝ) := (D (x + t • h) - D x) h
  have hDeriv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt g (g' t) (Icc 0 1) t := by
    have hline := hasDerivAt_line_of_hasLineDerivAt
      (hasLineDerivAt_of_smoothKernel hU hK (hseg t ht).1 h)
    rw [← kernelFDeriv_apply hU hK (hseg t ht).1 h] at hline
    change HasDerivWithinAt
      ((fun t => f (x + t • h)) - fun t => t • D x h) ((D (x + t • h) - D x) h) _ t
    simpa only [sub_apply, one_smul] using
      (hline.sub ((hasDerivAt_id' t).smul_const (D x h))).hasDerivWithinAt
  have hBound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : ‖g' t‖ ≤ ε * ‖h‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (by simpa only [dist_eq_norm] using (hseg t (Ico_subset_Icc_self ht)).2.le) (norm_nonneg h))
  change ‖f (x + h) - f x - D x h‖ ≤ ε * ‖h‖
  rw [sub_right_comm]
  simpa only [g, zero_smul, one_smul, add_zero, sub_zero] using
    norm_image_sub_le_of_norm_deriv_le_segment_01' hDeriv hBound

private theorem contDiffOn_of_smoothKernel {U : Set E} (hU : IsOpen U) {f : E → H}
    (hK : ContDiffOn ℝ ∞ (realKernel f) (U ×ˢ U)) : ContDiffOn ℝ ∞ f U := by
  rw [contDiffOn_infty]
  have order (n : ℕ) (g : E → H) (hg : ContDiffOn ℝ ∞ (realKernel g) (U ×ˢ U)) :
      ContDiffOn ℝ n g U := by
    induction n generalizing g with
    | zero =>
        exact contDiffOn_zero.mpr (continuousOn_of_continuousOn_realKernel hU hg.continuousOn)
    | succ n ih =>
        rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_apply hU.uniqueDiffOn]
        refine ⟨fun x hx => (hasFDerivAt_of_smoothKernel hU hg hx).differentiableAt.differentiableWithinAt,
          by simp, fun v => ?_⟩
        apply (ih _ (contDiffOn_realKernel_lineDeriv hU hg v)).congr
        intro x hx
        rw [(hasFDerivAt_of_smoothKernel hU hg hx).hasFDerivWithinAt.fderivWithin (hU.uniqueDiffOn x hx),
          kernelFDeriv_apply hU hg hx v]
  exact fun n => order n f hK

end ModelSpace

universe uA uM uH

/-- Neeb's smooth-kernel criterion for the finite-dimensional real manifold models in the Library. -/
theorem hilbertSmoothKernel : HilbertSmoothKernelStatement.{uA, uM, uH} := by
  intro A _ _ _ M _ _ _ H _ _ _ f
  constructor
  · intro hf
    exact (contDiff_inner (𝕜 := ℂ) (E := H) (n := ∞)).contMDiff.comp
      ((hf.comp contMDiff_fst).prodMk_space (hf.comp contMDiff_snd))
  · intro hK x
    let e : OpenPartialHomeomorph M A := chartAt A x
    have hInv : ContMDiffOn 𝓘(ℝ, A) 𝓘(ℝ, A) ∞ e.symm e.target :=
      contMDiffOn_chart_symm
    have hPair : ContMDiffOn 𝓘(ℝ, A × A) (𝓘(ℝ, A).prod 𝓘(ℝ, A)) ∞
        (fun p : A × A => (e.symm p.1, e.symm p.2)) (e.target ×ˢ e.target) :=
      (hInv.comp contDiff_fst.contMDiff.contMDiffOn mapsTo_fst_prod).prodMk
        (hInv.comp contDiff_snd.contMDiff.contMDiffOn mapsTo_snd_prod)
    let g : A → H := f ∘ e.symm
    let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
    have hgK : ContDiffOn ℝ ∞ (realKernel g) (e.target ×ˢ e.target) :=
      ((Complex.reCLM.contDiff.contMDiff.comp hK).comp_contMDiffOn hPair).contDiffOn
    have hg := (contDiffOn_of_smoothKernel e.open_target hgK).contMDiffOn
    have he : ContMDiffOn 𝓘(ℝ, A) 𝓘(ℝ, A) ∞ e e.source := contMDiffOn_chart
    have hBack : ContMDiffOn 𝓘(ℝ, A) 𝓘(ℝ, H) ∞ f e.source :=
      (hg.comp he e.mapsTo).congr fun y hy => (congrArg f (e.left_inv hy)).symm
    exact hBack.contMDiffAt (e.open_source.mem_nhds (mem_chart_source A x))

end Langlands.Archimedean
