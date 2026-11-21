import Langlands.Global.RankinSelberg.ArchimedeanGammaBounds
import Langlands.LocalFactor.Archimedean.RealTateProof
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# The theta identity for real Tate integrals

See the paired Markdown file.
-/

noncomputable section

open MeasureTheory Set Filter Complex
open scoped Topology Real SchwartzMap FourierTransform

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanTateTheta

open Langlands.LocalFactor.RealTate ArchimedeanMellinPair ArchimedeanInverseMellin

/-! ### Bounds and the functional equation on the critical strip -/

theorem norm_integrand (f : ℝ → ℂ) (e : Fin 2) (w : ℂ) {x : ℝ} (hx : x ≠ 0) :
    ‖integrand f e w x‖ = ‖f x‖ * |x| ^ (w.re - 1) := by
  have hpos : 0 < |x| := abs_pos.2 hx
  have hs : ‖((x / |x| : ℝ) : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_abs, div_self hpos.ne']
  simp only [integrand, hx, ↓reduceIte, norm_mul, norm_pow, hs, one_pow, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos hpos, sub_re, one_re]

/-- On a vertical strip `c ≤ Re w ≤ d` with `0 < c`, the zeta integral is bounded by a constant. -/
theorem norm_zeta_le (f : 𝓢(ℝ, ℂ)) (e : Fin 2) {c d : ℝ} (hc : 0 < c) {w : ℂ}
    (hcw : c ≤ w.re) (hwd : w.re ≤ d) :
    ‖zeta f e w‖ ≤ ∫ x, (‖integrand f 0 c x‖ + ‖integrand f 0 d x‖) := by
  have hic : Integrable (integrand f 0 c) := integrable_integrand f 0 (by simpa using hc)
  have hid : Integrable (integrand f 0 d) :=
    integrable_integrand f 0 (by simp only [ofReal_re]; linarith)
  refine (norm_integral_le_integral_norm _).trans
    (integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _) (hic.norm.add hid.norm)
      (ae_of_all _ fun x => ?_))
  by_cases hx : x = 0
  · simp [integrand, hx]
  · simp only [norm_integrand _ _ _ hx, ofReal_re]
    have hpos : 0 < |x| := abs_pos.2 hx
    have := rpow_le_add hpos (sub_le_sub_right hcw 1) (sub_le_sub_right hwd 1)
    calc ‖f x‖ * |x| ^ (w.re - 1) ≤ ‖f x‖ * (|x| ^ (c - 1) + |x| ^ (d - 1)) :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = ‖f x‖ * |x| ^ (c - 1) + ‖f x‖ * |x| ^ (d - 1) := by ring

/-- The two expressions for `Z(f, e, w) / Γ_ℝ(w + e)` on the critical strip. -/
theorem ratio_eq_dual (f : 𝓢(ℝ, ℂ)) (e : Fin 2) {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    zeta f e w * (Gammaℝ (w + e.val))⁻¹ =
      zeta (𝓕⁻ f : 𝓢(ℝ, ℂ)) e (1 - w) * (I ^ e.val * Gammaℝ (1 - w + e.val))⁻¹ := by
  have hΓ1 := Gammaℝ_ne_zero_of_re_pos (re_add_pos h0 e)
  have hΓ2 := Gammaℝ_ne_zero_of_re_pos (re_one_sub_add_pos h1 e)
  have hI : I ^ e.val ≠ 0 := pow_ne_zero _ I_ne_zero
  have h := zeta_fourierInv_mul_Gammaℝ f e h0 h1
  field_simp
  first | linear_combination h | linear_combination -h

/-! ### Continuity of inverse Mellin transforms and of theta functions -/

theorem rpow_le_of_mem {t a b : ℝ} (ha : 0 < a) (hat : a ≤ t) (htb : t ≤ b) (p : ℝ) :
    t ^ p ≤ a ^ p + b ^ p := by
  rcases le_total 0 p with hp | hp
  · exact (Real.rpow_le_rpow (ha.le.trans hat) htb hp).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg ha.le _))
  · exact (Real.rpow_le_rpow_of_nonpos ha hat hp).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg (ha.le.trans (hat.trans htb)) _))

/-- An inverse Mellin transform along a line where the function is integrable is continuous on
`(0, ∞)`. -/
theorem continuousAt_mellinInv {m : ℂ → ℂ} (hm : Continuous m) (c : ℝ)
    (hint : Integrable (fun y : ℝ => ‖m (c + y * I)‖)) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ContinuousAt (mellinInv c m) t₀ := by
  unfold mellinInv
  refine ContinuousAt.const_smul ?_ _
  set B : ℝ := (t₀ / 2) ^ (-c) + (2 * t₀) ^ (-c) with hB
  have hline : Continuous (fun y : ℝ => (c : ℂ) + y * I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hnhds : Ioo (t₀ / 2) (2 * t₀) ∈ 𝓝 t₀ := Ioo_mem_nhds (by linarith) (by linarith)
  refine continuousAt_of_dominated (bound := fun y => B * ‖m (c + y * I)‖) ?_ ?_
    (hint.const_mul B) ?_
  · filter_upwards [hnhds] with t ht
    have htpos : 0 < t := by linarith [ht.1]
    have h1 : Continuous (fun y : ℝ => (t : ℂ) ^ (-((c : ℂ) + y * I))) :=
      hline.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.2 htpos.ne'))
    exact (h1.smul (hm.comp hline)).aestronglyMeasurable
  · filter_upwards [hnhds] with t ht
    have htpos : 0 < t := by linarith [ht.1]
    refine ae_of_all _ fun y => ?_
    rw [norm_smul, norm_ofReal_cpow_neg htpos]
    exact mul_le_mul_of_nonneg_right
      (rpow_le_of_mem (by linarith) ht.1.le ht.2.le (-c)) (norm_nonneg _)
  · refine ae_of_all _ fun y => ?_
    have h1 : ContinuousAt (fun t : ℝ => (t : ℂ) ^ (-((c : ℂ) + y * I))) t₀ :=
      Complex.continuous_ofReal.continuousAt.cpow continuousAt_const
        (Complex.ofReal_mem_slitPlane.2 ht₀)
    exact h1.smul continuousAt_const

/-- The theta function of a continuous rapidly decreasing function is continuous on `(0, ∞)`. -/
theorem continuousAt_theta {X : Type*} [MeasurableSpace X] (μ : Measure X) (F : X → ℂ)
    (δ : X → ℝ) (hF : AEStronglyMeasurable F μ) (hδm : Measurable δ) (hδ : ∀ x, 0 < δ x)
    {h : ℝ → ℂ} (hh : Measurable h) (hcont : ∀ t, 0 < t → ContinuousAt h t)
    (hdec : RapidDecay h) {M : ℝ} (hint : Integrable (fun x => ‖F x‖ * δ x ^ M) μ)
    {t₀ : ℝ} (ht₀ : 0 < t₀) : ContinuousAt (theta μ F δ h) t₀ := by
  obtain ⟨C, hC⟩ := hdec M
  have hC0 := RapidDecay.nonneg_const hC
  set B : ℝ := C * ((t₀ / 2) ^ M + (2 * t₀) ^ M) with hB
  have hnhds : Ioo (t₀ / 2) (2 * t₀) ∈ 𝓝 t₀ := Ioo_mem_nhds (by linarith) (by linarith)
  refine continuousAt_of_dominated (bound := fun x => B * (‖F x‖ * δ x ^ M)) ?_ ?_
    (hint.const_mul B) ?_
  · exact Eventually.of_forall fun a =>
      hF.mul (hh.comp (measurable_const.mul hδm)).aestronglyMeasurable
  · filter_upwards [hnhds] with a ha
    have hapos : 0 < a := by linarith [ha.1]
    refine ae_of_all _ fun x => ?_
    rw [norm_mul]
    have h1 := hC (a * δ x) (mul_pos hapos (hδ x))
    rw [Real.mul_rpow hapos.le (hδ x).le] at h1
    have h2 : a ^ M ≤ (t₀ / 2) ^ M + (2 * t₀) ^ M :=
      rpow_le_of_mem (by linarith) ha.1.le ha.2.le M
    have hδM : 0 ≤ δ x ^ M := Real.rpow_nonneg (hδ x).le M
    calc ‖F x‖ * ‖h (a * δ x)‖ ≤ ‖F x‖ * (C * (a ^ M * δ x ^ M)) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = C * a ^ M * (‖F x‖ * δ x ^ M) := by ring
      _ ≤ B * (‖F x‖ * δ x ^ M) := by
          rw [hB]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hC0)
            (mul_nonneg (norm_nonneg _) hδM)
  · refine ae_of_all _ fun x => ?_
    exact continuousAt_const.mul (ContinuousAt.comp (f := fun a : ℝ => a * δ x)
      (hcont _ (mul_pos ht₀ (hδ x))) (continuousAt_id.mul continuousAt_const))

/-! ### The pair for the real character `sgn^e |·|^u` -/

/-- `I^e exp(w²) / Γ_ℝ(u + e - w)`, the Mellin transform of the first function of the pair. -/
def pairMh (e : Fin 2) (u : ℂ) (w : ℂ) : ℂ :=
  I ^ e.val * Complex.exp (w ^ 2) * (Gammaℝ (-w + u + e.val))⁻¹

/-- `exp((w + 1)²) / Γ_ℝ(e - u - w)`, the Mellin transform of the second function. -/
def pairMk (e : Fin 2) (u : ℂ) (w : ℂ) : ℂ :=
  Complex.exp ((w + 1) ^ 2) * (Gammaℝ (-w - u + e.val))⁻¹

/-- The first function of the pair. -/
def pairH (e : Fin 2) (u : ℂ) : ℝ → ℂ := mellinInv 0 (pairMh e u)

/-- The second function of the pair. -/
def pairK (e : Fin 2) (u : ℂ) : ℝ → ℂ := mellinInv 0 (pairMk e u)

theorem differentiable_pairMh (e : Fin 2) (u : ℂ) : Differentiable ℂ (pairMh e u) :=
  ((differentiable_const _).mul (Complex.differentiable_exp.comp (differentiable_id.pow 2))).mul
    (Complex.differentiable_Gammaℝ_inv.comp
      ((differentiable_neg.add_const _).add_const _))

theorem differentiable_pairMk (e : Fin 2) (u : ℂ) : Differentiable ℂ (pairMk e u) :=
  (Complex.differentiable_exp.comp ((differentiable_id.add_const 1).pow 2)).mul
    (Complex.differentiable_Gammaℝ_inv.comp
      ((differentiable_neg.sub_const _).add_const _))

theorem stripDecay_pairMh (e : Fin 2) (u : ℂ) : StripDecay (pairMh e u) := by
  have hF : StripExpType (fun w : ℂ => I ^ e.val * (Gammaℝ (-w + u + e.val))⁻¹) := by
    refine ((StripExpType.const (I ^ e.val)).mul
      ((inv_Gammaℝ_stripExpType.comp_ofReal_mul (-1)).comp_add (-(u + e.val)))).congr
      fun w => ?_
    have hs : ((-1 : ℝ) : ℂ) * (w + -(u + ((e.val : ℕ) : ℂ))) = -w + u + (e.val : ℂ) := by
      push_cast; ring
    simp only [hs]
  refine (stripDecay_exp_sq_mul hF).congr fun w => ?_
  simp only [pairMh]
  ring

theorem stripDecay_pairMk (e : Fin 2) (u : ℂ) : StripDecay (pairMk e u) := by
  have hF : StripExpType (fun v : ℂ => (Gammaℝ (1 - v - u + e.val))⁻¹) := by
    refine ((inv_Gammaℝ_stripExpType.comp_ofReal_mul (-1)).comp_add
      (-(1 - u + e.val))).congr fun v => ?_
    have hs : ((-1 : ℝ) : ℂ) * (v + -(1 - u + ((e.val : ℕ) : ℂ))) = 1 - v - u + (e.val : ℂ) := by
      push_cast; ring
    simp only [hs]
  refine ((stripDecay_exp_sq_mul hF).comp_add_ofReal 1).congr fun w => ?_
  have hw : (1 : ℂ) - (w + 1) - u + ((e.val : ℕ) : ℂ) = -w - u + ((e.val : ℕ) : ℂ) := by ring
  simp only [pairMk, ofReal_one, hw]

theorem integrable_line_of_stripDecay {m : ℂ → ℂ} (hm : Continuous m) (hdec : StripDecay m)
    (c : ℝ) : Integrable (fun y : ℝ => ‖m (c + y * I)‖) := by
  obtain ⟨C, hC⟩ := hdec c c
  exact (integrable_vertical hm (hC c le_rfl le_rfl)).norm

theorem measurable_pairH (e : Fin 2) (u : ℂ) : Measurable (pairH e u) :=
  measurable_mellinInv (differentiable_pairMh e u).continuous 0

theorem measurable_pairK (e : Fin 2) (u : ℂ) : Measurable (pairK e u) :=
  measurable_mellinInv (differentiable_pairMk e u).continuous 0

theorem rapidDecay_pairH (e : Fin 2) (u : ℂ) : RapidDecay (pairH e u) :=
  rapidDecay_mellinInv (differentiable_pairMh e u) (stripDecay_pairMh e u)

theorem rapidDecay_pairK (e : Fin 2) (u : ℂ) : RapidDecay (pairK e u) :=
  rapidDecay_mellinInv (differentiable_pairMk e u) (stripDecay_pairMk e u)

theorem mellin_pairH (e : Fin 2) (u : ℂ) (w : ℂ) : mellin (pairH e u) w = pairMh e u w :=
  mellin_mellinInv (differentiable_pairMh e u) (stripDecay_pairMh e u) w

theorem mellin_pairK (e : Fin 2) (u : ℂ) (w : ℂ) : mellin (pairK e u) w = pairMk e u w :=
  mellin_mellinInv (differentiable_pairMk e u) (stripDecay_pairMk e u) w

theorem continuousAt_pairH (e : Fin 2) (u : ℂ) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (pairH e u) t :=
  continuousAt_mellinInv (differentiable_pairMh e u).continuous 0
    (integrable_line_of_stripDecay (differentiable_pairMh e u).continuous
      (stripDecay_pairMh e u) 0) ht

theorem continuousAt_pairK (e : Fin 2) (u : ℂ) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (pairK e u) t :=
  continuousAt_mellinInv (differentiable_pairMk e u).continuous 0
    (integrable_line_of_stripDecay (differentiable_pairMk e u).continuous
      (stripDecay_pairMk e u) 0) ht


/-! ### The theta identity on the real line -/

/-- `|x|`, replaced by `1` at `x = 0` (a positive function equal to `|x|` almost everywhere). -/
def absPos (x : ℝ) : ℝ := if x = 0 then 1 else |x|

theorem absPos_pos (x : ℝ) : 0 < absPos x := by
  unfold absPos
  split_ifs with h
  · exact one_pos
  · exact abs_pos.2 h

theorem measurable_absPos : Measurable absPos :=
  Measurable.ite (measurableSet_singleton (0 : ℝ)) measurable_const continuous_abs.measurable

theorem integrand_mul_cpow (f : ℝ → ℂ) (e : Fin 2) (u s : ℂ) (x : ℝ) :
    integrand f e u x * ((absPos x : ℝ) : ℂ) ^ s = integrand f e (u + s) x := by
  by_cases hx : x = 0
  · simp [integrand, hx]
  · have hne : ((|x| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (abs_pos.2 hx).ne'
    simp only [integrand, absPos, hx, ↓reduceIte]
    rw [mul_assoc, ← cpow_add _ _ hne]
    congr 2
    ring

theorem norm_integrand_mul_rpow (f : ℝ → ℂ) (e : Fin 2) (u : ℂ) (σ : ℝ) (x : ℝ) :
    ‖integrand f e u x‖ * absPos x ^ σ = ‖integrand f 0 (u + σ) x‖ := by
  by_cases hx : x = 0
  · simp [integrand, hx]
  · have hpos : 0 < |x| := abs_pos.2 hx
    rw [norm_integrand f e u hx, norm_integrand f 0 _ hx]
    simp only [absPos, hx, ↓reduceIte, add_re, ofReal_re]
    rw [mul_assoc, ← Real.rpow_add hpos]
    congr 2
    ring

theorem integrable_norm_mul_rpow (f : 𝓢(ℝ, ℂ)) (e : Fin 2) (u : ℂ) (σ : ℝ)
    (h : 0 < u.re + σ) : Integrable (fun x => ‖integrand f e u x‖ * absPos x ^ σ) := by
  have := (integrable_integrand f 0 (u := u + σ) (by simpa using h)).norm
  exact this.congr (ae_of_all _ fun x => (norm_integrand_mul_rpow f e u σ x).symm)

theorem integral_integrand_mul_cpow (f : ℝ → ℂ) (e : Fin 2) (u s : ℂ) :
    ∫ x, integrand f e u x * ((absPos x : ℝ) : ℂ) ^ s = zeta f e (u + s) :=
  integral_congr_ae (ae_of_all _ fun x => integrand_mul_cpow f e u s x)

theorem norm_inv_smul_le {g : ℝ → ℂ} {C M : ℝ} (hg : ∀ b : ℝ, 0 < b → ‖g b‖ ≤ C * b ^ M)
    {t : ℝ} (ht : 0 < t) : ‖(t : ℂ) ^ (1 : ℂ) • g t⁻¹‖ ≤ C * t ^ (1 - M) := by
  rw [norm_smul, Complex.cpow_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have h1 := hg t⁻¹ (inv_pos.2 ht)
  rw [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le] at h1
  calc t * ‖g t⁻¹‖ ≤ t * (C * t ^ (-M)) := mul_le_mul_of_nonneg_left h1 ht.le
    _ = C * t ^ (1 - M) := by
        rw [Real.rpow_sub ht, Real.rpow_one, Real.rpow_neg ht.le, div_eq_mul_inv]
        ring

theorem isBigO_atTop_of_bound {g : ℝ → ℂ} {C M : ℝ} (hg : ∀ t : ℝ, 0 < t → ‖g t‖ ≤ C * t ^ M) :
    g =O[atTop] (· ^ M) := by
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht.le _)]
  exact hg t ht

theorem isBigO_nhdsGT_of_bound {g : ℝ → ℂ} {C M : ℝ} (hg : ∀ t : ℝ, 0 < t → ‖g t‖ ≤ C * t ^ M) :
    g =O[𝓝[>] 0] (· ^ M) := by
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht.le _)]
  exact hg t ht

/-- The theta identity (Jacquet 2009, Proposition 4.2, for the real Tate integral): for a
Schwartz function `f`, with `F(x) = f(x) sgn(x)^e |x|^(u-1)` and
`F'(x) = f̂(x) sgn(x)^e |x|^(-u-1)` (`f̂ = 𝓕⁻ f`),
`∫ F(x) h(a|x|) dx = a ∫ F'(x) k(a⁻¹|x|) dx` for every `a > 0`. -/
theorem theta_identity (f : 𝓢(ℝ, ℂ)) (e : Fin 2) (u : ℂ) {a : ℝ} (ha : 0 < a) :
    theta volume (integrand f e u) absPos (pairH e u) a =
      (a : ℂ) * theta volume (integrand (𝓕⁻ f : 𝓢(ℝ, ℂ)) e (-u)) absPos (pairK e u) a⁻¹ := by
  set F := integrand f e u with hFdef
  set F' := integrand (𝓕⁻ f : 𝓢(ℝ, ℂ)) e (-u) with hF'def
  have hFm : AEStronglyMeasurable F volume :=
    (measurable_integrand f.continuous.measurable e u).aestronglyMeasurable
  have hF'm : AEStronglyMeasurable F' volume :=
    (measurable_integrand (𝓕⁻ f : 𝓢(ℝ, ℂ)).continuous.measurable e (-u)).aestronglyMeasurable
  set θ1 := theta volume F absPos (pairH e u) with hθ1
  set θ2 := theta volume F' absPos (pairK e u) with hθ2
  set φ2 : ℝ → ℂ := fun t => (t : ℂ) ^ (1 : ℂ) • θ2 t⁻¹ with hφ2
  set σ : ℝ := u.re - 1 / 2 with hσ
  have hFint : ∀ M : ℝ, 0 < u.re + M → Integrable (fun x => ‖F x‖ * absPos x ^ M) :=
    fun M hM => integrable_norm_mul_rpow f e u M hM
  have hF'int : ∀ M : ℝ, u.re < M → Integrable (fun x => ‖F' x‖ * absPos x ^ M) :=
    fun M hM => integrable_norm_mul_rpow _ e (-u) M (by simp only [neg_re]; linarith)
  have hθ1c : ∀ t : ℝ, 0 < t → ContinuousAt θ1 t := fun t ht =>
    continuousAt_theta volume F absPos hFm measurable_absPos absPos_pos (measurable_pairH e u)
      (fun b hb => continuousAt_pairH e u hb) (rapidDecay_pairH e u)
      (hFint (1 - u.re) (by linarith)) ht
  have hθ2c : ∀ t : ℝ, 0 < t → ContinuousAt θ2 t := fun t ht =>
    continuousAt_theta volume F' absPos hF'm measurable_absPos absPos_pos (measurable_pairK e u)
      (fun b hb => continuousAt_pairK e u hb) (rapidDecay_pairK e u)
      (hF'int (u.re + 1) (by linarith)) ht
  have hφ2c : ∀ t : ℝ, 0 < t → ContinuousAt φ2 t := fun t ht =>
    (Complex.continuous_ofReal.continuousAt.cpow continuousAt_const
      (Complex.ofReal_mem_slitPlane.2 ht)).smul
      (ContinuousAt.comp (g := θ2) (f := fun b : ℝ => b⁻¹) (hθ2c _ (inv_pos.2 ht))
        (continuousAt_inv₀ ht.ne'))
  -- Mellin convergence on the line `Re w = σ`
  have hθ1conv : MellinConvergent θ1 (σ : ℂ) := by
    obtain ⟨C1, -, hC1⟩ := theta_bound volume F absPos absPos_pos (rapidDecay_pairH e u)
      (hFint (-(u.re - 1 / 4)) (by linarith))
    obtain ⟨C2, -, hC2⟩ := theta_bound volume F absPos absPos_pos (rapidDecay_pairH e u)
      (hFint (-(σ - 1)) (by rw [hσ]; linarith))
    refine mellinConvergent_of_isBigO_rpow (a := u.re - 1 / 4) (b := σ - 1) ?_
      (isBigO_atTop_of_bound hC1) (by rw [ofReal_re, hσ]; linarith)
      (isBigO_nhdsGT_of_bound hC2) (by rw [ofReal_re]; linarith)
    exact ContinuousOn.locallyIntegrableOn (fun t ht => (hθ1c t ht).continuousWithinAt)
      measurableSet_Ioi
  have hφ2conv : MellinConvergent φ2 (σ : ℂ) := by
    obtain ⟨C1, -, hC1⟩ := theta_bound volume F' absPos absPos_pos (rapidDecay_pairK e u)
      (hF'int (1 + (u.re - 1 / 4)) (by linarith))
    obtain ⟨C2, -, hC2⟩ := theta_bound volume F' absPos absPos_pos (rapidDecay_pairK e u)
      (hF'int (1 + (σ - 1 / 4)) (by rw [hσ]; linarith))
    have hb1 : ∀ t : ℝ, 0 < t → ‖φ2 t‖ ≤ C1 * t ^ (-(u.re - 1 / 4)) := fun t ht => by
      have := norm_inv_smul_le hC1 ht
      rwa [show (1 : ℝ) - (1 + (u.re - 1 / 4)) = -(u.re - 1 / 4) by ring] at this
    have hb2 : ∀ t : ℝ, 0 < t → ‖φ2 t‖ ≤ C2 * t ^ (-(σ - 1 / 4)) := fun t ht => by
      have := norm_inv_smul_le hC2 ht
      rwa [show (1 : ℝ) - (1 + (σ - 1 / 4)) = -(σ - 1 / 4) by ring] at this
    refine mellinConvergent_of_isBigO_rpow (a := u.re - 1 / 4) (b := σ - 1 / 4) ?_
      (isBigO_atTop_of_bound hb1) (by rw [ofReal_re, hσ]; linarith)
      (isBigO_nhdsGT_of_bound hb2) (by rw [ofReal_re]; linarith)
    exact ContinuousOn.locallyIntegrableOn (fun t ht => (hφ2c t ht).continuousWithinAt)
      measurableSet_Ioi
  -- the two Mellin transforms on the line
  have hline1 : ∀ y : ℝ, mellin θ1 ((σ : ℂ) + y * I) =
      zeta f e (u - ((σ : ℂ) + y * I)) * pairMh e u ((σ : ℂ) + y * I) := by
    intro y
    set s : ℂ := -((σ : ℂ) + y * I) with hs
    have hsre : s.re = -σ := by simp [hs]
    have h := mellin_theta volume F absPos hFm measurable_absPos absPos_pos (pairH e u)
      (measurable_pairH e u) (rapidDecay_pairH e u) s
      (by rw [hsre]; exact hFint _ (by rw [hσ]; linarith))
    rw [hs, neg_neg] at h
    rw [h, integral_integrand_mul_cpow, mellin_pairH, ← sub_eq_add_neg]
  have hline2 : ∀ y : ℝ, mellin φ2 ((σ : ℂ) + y * I) =
      zeta (𝓕⁻ f : 𝓢(ℝ, ℂ)) e (1 - u + ((σ : ℂ) + y * I)) *
        pairMk e u (-((σ : ℂ) + y * I) - 1) := by
    intro y
    set w : ℂ := (σ : ℂ) + y * I with hw
    have hwre : w.re = σ := by simp [hw]
    have h := mellin_theta volume F' absPos hF'm measurable_absPos absPos_pos (pairK e u)
      (measurable_pairK e u) (rapidDecay_pairK e u) (w + 1)
      (by rw [add_re, one_re, hwre]; exact hF'int _ (by rw [hσ]; linarith))
    rw [hφ2, mellin_cpow_smul, mellin_comp_inv, h, integral_integrand_mul_cpow, mellin_pairK]
    congr 2 <;> ring
  -- equality on the line, from the functional equation on the critical strip
  have hline : ∀ y : ℝ, mellin θ1 ((σ : ℂ) + y * I) = mellin φ2 ((σ : ℂ) + y * I) := by
    intro y
    rw [hline1, hline2]
    set w : ℂ := u - ((σ : ℂ) + y * I) with hw
    have hwre : w.re = 1 / 2 := by simp [hw, hσ]
    have key := ratio_eq_dual f e (w := w) (by rw [hwre]; norm_num) (by rw [hwre]; norm_num)
    have hI : I ^ e.val ≠ 0 := pow_ne_zero _ I_ne_zero
    have e1 : 1 - u + ((σ : ℂ) + y * I) = 1 - w := by rw [hw]; ring
    have e2 : pairMh e u ((σ : ℂ) + y * I) =
        I ^ e.val * Complex.exp (((σ : ℂ) + y * I) ^ 2) * (Gammaℝ (w + e.val))⁻¹ := by
      rw [pairMh, hw]; congr 3; ring
    have e3 : pairMk e u (-((σ : ℂ) + y * I) - 1) =
        Complex.exp (((σ : ℂ) + y * I) ^ 2) * (Gammaℝ (1 - w + e.val))⁻¹ := by
      rw [pairMk, hw]
      congr 2
      · ring
      · congr 1; ring
    rw [e1, e2, e3]
    calc zeta f e w * (I ^ e.val * Complex.exp (((σ : ℂ) + y * I) ^ 2) *
          (Gammaℝ (w + e.val))⁻¹)
        = I ^ e.val * Complex.exp (((σ : ℂ) + y * I) ^ 2) *
            (zeta f e w * (Gammaℝ (w + e.val))⁻¹) := by ring
      _ = I ^ e.val * Complex.exp (((σ : ℂ) + y * I) ^ 2) *
            (zeta (𝓕⁻ f : 𝓢(ℝ, ℂ)) e (1 - w) * (I ^ e.val * Gammaℝ (1 - w + e.val))⁻¹) := by
          rw [key]
      _ = (I ^ e.val * (I ^ e.val)⁻¹) * (zeta (𝓕⁻ f : 𝓢(ℝ, ℂ)) e (1 - w) *
            (Complex.exp (((σ : ℂ) + y * I) ^ 2) * (Gammaℝ (1 - w + e.val))⁻¹)) := by
          rw [mul_inv]; ring
      _ = _ := by rw [mul_inv_cancel₀ hI, one_mul]
  -- vertical integrability of the Mellin transform of `θ1` on the line
  have hvert : VerticalIntegrable (mellin θ1) σ := by
    obtain ⟨C, hC⟩ := stripDecay_pairMh e u σ σ
    set B := ∫ x, (‖integrand f 0 ((1 / 2 : ℝ) : ℂ) x‖ + ‖integrand f 0 ((1 / 2 : ℝ) : ℂ) x‖)
    have hcont : Continuous (fun y : ℝ => zeta f e (u - ((σ : ℂ) + y * I)) *
        pairMh e u ((σ : ℂ) + y * I)) := by
      have hl : Continuous (fun y : ℝ => (σ : ℂ) + y * I) :=
        continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
      refine (continuous_iff_continuousAt.2 fun y => ?_).mul
        ((differentiable_pairMh e u).continuous.comp hl)
      have hre : 0 < (u - ((σ : ℂ) + y * I)).re := by simp [hσ]
      exact ContinuousAt.comp (g := zeta f e) (f := fun y : ℝ => u - ((σ : ℂ) + y * I))
        (differentiableAt_zeta f e hre).continuousAt (continuous_const.sub hl).continuousAt
    refine (((integrable_inv_one_add_sq).const_mul (B * C)).mono' hcont.aestronglyMeasurable
      (ae_of_all _ fun y => ?_)).congr (ae_of_all _ fun y => (hline1 y).symm)
    rw [norm_mul]
    have hz : ‖zeta f e (u - ((σ : ℂ) + y * I))‖ ≤ B :=
      norm_zeta_le f e (c := 1 / 2) (d := 1 / 2) (by norm_num) (by simp [hσ]) (by simp [hσ])
    have hB : 0 ≤ B := integral_nonneg fun x => by positivity
    calc ‖zeta f e (u - ((σ : ℂ) + y * I))‖ * ‖pairMh e u ((σ : ℂ) + y * I)‖
        ≤ B * (C * (1 + y ^ 2)⁻¹) := mul_le_mul hz (hC σ le_rfl le_rfl y) (norm_nonneg _) hB
      _ = B * C * (1 + y ^ 2)⁻¹ := by ring
  -- Mellin inversion on both sides
  have hvert2 : VerticalIntegrable (mellin φ2) σ := by
    refine hvert.congr (ae_of_all _ fun y => ?_)
    exact hline y
  have h1 := mellinInv_mellin_eq σ θ1 ha hθ1conv hvert (hθ1c a ha)
  have h2 := mellinInv_mellin_eq σ φ2 ha hφ2conv hvert2 (hφ2c a ha)
  have h3 : mellinInv σ (mellin θ1) a = mellinInv σ (mellin φ2) a := by
    unfold mellinInv
    congr 2
    funext y
    rw [hline y]
  rw [← h1, h3, h2, hφ2]
  simp only [Complex.cpow_one, smul_eq_mul]


/-! ### The pair kernels as inverse Fourier transforms -/

/-- A rapidly decreasing function gives `|x|^(Re w - 1) ‖h(c|x|)‖ ≤ B (1 + x²)⁻¹`. -/
theorem exists_bound_of_rapidDecay {h : ℝ → ℂ} (hdec : RapidDecay h) {c : ℝ} (hc : 0 < c)
    (w : ℂ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, x ≠ 0 →
      |x| ^ (w.re - 1) * ‖h (c * |x|)‖ ≤ B * (1 + x ^ 2)⁻¹ := by
  obtain ⟨C1, hC1⟩ := hdec (1 - w.re)
  obtain ⟨C3, hC3⟩ := hdec (-1 - w.re)
  have hC1' := RapidDecay.nonneg_const hC1
  have hC3' := RapidDecay.nonneg_const hC3
  refine ⟨C1 * c ^ (1 - w.re) + C3 * c ^ (-1 - w.re), by positivity, fun x hx => ?_⟩
  have hpos : 0 < |x| := abs_pos.2 hx
  have hcx : 0 < c * |x| := mul_pos hc hpos
  have h1 := hC1 _ hcx
  have h3 := hC3 _ hcx
  rw [Real.mul_rpow hc.le hpos.le] at h1 h3
  have hsq : (0 : ℝ) < 1 + x ^ 2 := by positivity
  rw [le_mul_inv_iff₀ hsq]
  have hx2 : x ^ 2 = |x| ^ (2 : ℝ) := by
    rw [Real.rpow_two, sq_abs]
  have hA : |x| ^ (w.re - 1) * ‖h (c * |x|)‖ ≤ C1 * c ^ (1 - w.re) := by
    calc |x| ^ (w.re - 1) * ‖h (c * |x|)‖
        ≤ |x| ^ (w.re - 1) * (C1 * (c ^ (1 - w.re) * |x| ^ (1 - w.re))) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hpos.le _)
      _ = C1 * c ^ (1 - w.re) * (|x| ^ (w.re - 1) * |x| ^ (1 - w.re)) := by ring
      _ = C1 * c ^ (1 - w.re) := by
          rw [← Real.rpow_add hpos, show w.re - 1 + (1 - w.re) = 0 by ring, Real.rpow_zero,
            mul_one]
  have hB : |x| ^ (w.re - 1) * ‖h (c * |x|)‖ * x ^ 2 ≤ C3 * c ^ (-1 - w.re) := by
    rw [hx2]
    calc |x| ^ (w.re - 1) * ‖h (c * |x|)‖ * |x| ^ (2 : ℝ)
        ≤ |x| ^ (w.re - 1) * (C3 * (c ^ (-1 - w.re) * |x| ^ (-1 - w.re))) * |x| ^ (2 : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hpos.le _))
            (Real.rpow_nonneg hpos.le _)
      _ = C3 * c ^ (-1 - w.re) * (|x| ^ (w.re - 1) * |x| ^ (-1 - w.re) * |x| ^ (2 : ℝ)) := by
          ring
      _ = C3 * c ^ (-1 - w.re) := by
          rw [← Real.rpow_add hpos, ← Real.rpow_add hpos,
            show w.re - 1 + (-1 - w.re) + 2 = 0 by ring, Real.rpow_zero, mul_one]
  nlinarith

/-- `x ↦ g(c δ(x)) sgn(x)^e |x|^(w-1)` is integrable for a rapidly decreasing measurable `g`. -/
theorem integrable_kernel {g : ℝ → ℂ} (hg : Measurable g) (hdec : RapidDecay g) {c : ℝ}
    (hc : 0 < c) (e : Fin 2) (w : ℂ) :
    Integrable (integrand (fun x => g (c * absPos x)) e w) := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_of_rapidDecay hdec hc w
  refine ((integrable_inv_one_add_sq).const_mul B).mono'
    (measurable_integrand (hg.comp (measurable_const.mul measurable_absPos)) e w).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  by_cases hx : x = 0
  · simp only [integrand, hx, ↓reduceIte, norm_zero]
    exact mul_nonneg hB0 (by positivity)
  · rw [norm_integrand _ e w hx]
    simp only [absPos, hx, ↓reduceIte]
    rw [mul_comm]
    exact hB x hx

/-- The inverse Fourier integral `x ↦ ∫ e^(2π i x y) g(y) dy`. -/
def fourierInvInt (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y : ℝ, Complex.exp (2 * (π : ℂ) * I * ((x * y : ℝ) : ℂ)) * g y

theorem norm_exp_two_pi_I_mul' (t : ℝ) : ‖Complex.exp (2 * (π : ℂ) * I * (t : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem continuous_fourierInvInt {g : ℝ → ℂ} (hg : Integrable g) :
    Continuous (fourierInvInt g) := by
  refine continuous_of_dominated (bound := fun y => ‖g y‖) (fun x => ?_) (fun x => ?_)
    hg.norm ?_
  · have : Continuous (fun y : ℝ => Complex.exp (2 * (π : ℂ) * I * ((x * y : ℝ) : ℂ))) := by
      fun_prop
    exact this.aestronglyMeasurable.mul hg.aestronglyMeasurable
  · exact ae_of_all _ fun y => by rw [norm_mul, norm_exp_two_pi_I_mul', one_mul]
  · exact ae_of_all _ fun y => by fun_prop

/-- `∫ f̂ g = ∫ f · (inverse Fourier integral of g)` for Schwartz `f` and integrable `g`. -/
theorem integral_fourierInv_mul (f : 𝓢(ℝ, ℂ)) {g : ℝ → ℂ} (hg : Integrable g) :
    ∫ y, (𝓕⁻ f : 𝓢(ℝ, ℂ)) y * g y = ∫ x, f x * fourierInvInt g x := by
  have hint : Integrable (fun p : ℝ × ℝ =>
      Complex.exp (2 * (π : ℂ) * I * ((p.1 * p.2 : ℝ) : ℂ)) * f p.1 * g p.2)
      (volume.prod volume) := by
    refine ((SchwartzMap.integrable (μ := volume) f).mul_prod hg).norm.mono' ?_ (ae_of_all _ fun p => ?_)
    · have : Continuous (fun p : ℝ × ℝ =>
          Complex.exp (2 * (π : ℂ) * I * ((p.1 * p.2 : ℝ) : ℂ))) := by fun_prop
      exact (this.aestronglyMeasurable.mul (f.continuous.comp continuous_fst).aestronglyMeasurable).mul
        (hg.aestronglyMeasurable.comp_snd)
    · rw [norm_mul, norm_mul, norm_exp_two_pi_I_mul', one_mul, norm_mul]
  calc ∫ y, (𝓕⁻ f : 𝓢(ℝ, ℂ)) y * g y
      = ∫ y, ∫ x, Complex.exp (2 * (π : ℂ) * I * ((x * y : ℝ) : ℂ)) * f x * g y := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        dsimp only
        rw [fourierInv_apply_real, ← integral_mul_const]
    _ = ∫ x, ∫ y, Complex.exp (2 * (π : ℂ) * I * ((x * y : ℝ) : ℂ)) * f x * g y :=
        (integral_integral_swap hint).symm
    _ = ∫ x, f x * fourierInvInt g x := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        dsimp only
        unfold fourierInvInt
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        dsimp only
        ring

/-- The first pair kernel `x ↦ sgn(x)^e |x|^(u-1) h(a|x|)`. -/
def kernelH (e : Fin 2) (u : ℂ) (a : ℝ) : ℝ → ℂ :=
  integrand (fun x => pairH e u (a * absPos x)) e u

/-- The second pair kernel `y ↦ sgn(y)^e |y|^(-u-1) k(b|y|)`. -/
def kernelK (e : Fin 2) (u : ℂ) (b : ℝ) : ℝ → ℂ :=
  integrand (fun y => pairK e u (b * absPos y)) e (-u)

theorem integrand_mul_pair (f g : ℝ → ℂ) (e : Fin 2) (u : ℂ) (x : ℝ) :
    integrand f e u x * g x = f x * integrand g e u x := by
  by_cases hx : x = 0
  · simp [integrand, hx]
  · simp only [integrand, hx, ↓reduceIte]
    ring

/-- The first pair kernel is, almost everywhere, `a` times the inverse Fourier integral of
the second pair kernel with the inverse scaling. -/
theorem kernelH_ae_eq (e : Fin 2) (u : ℂ) {a : ℝ} (ha : 0 < a) :
    kernelH e u a =ᵐ[volume] fun x => (a : ℂ) * fourierInvInt (kernelK e u a⁻¹) x := by
  have hH : Integrable (kernelH e u a) :=
    integrable_kernel (measurable_pairH e u) (rapidDecay_pairH e u) ha e u
  have hK : Integrable (kernelK e u a⁻¹) :=
    integrable_kernel (measurable_pairK e u) (rapidDecay_pairK e u) (inv_pos.2 ha) e (-u)
  have key : ∀ f : 𝓢(ℝ, ℂ), ∫ x, f x * kernelH e u a x =
      ∫ x, f x * ((a : ℂ) * fourierInvInt (kernelK e u a⁻¹) x) := by
    intro f
    have h : ∫ x, integrand f e u x * pairH e u (a * absPos x) =
        (a : ℂ) * ∫ x, integrand (𝓕⁻ f : 𝓢(ℝ, ℂ)) e (-u) x * pairK e u (a⁻¹ * absPos x) :=
      theta_identity f e u ha
    have h1 : ∫ x, integrand f e u x * pairH e u (a * absPos x) = ∫ x, f x * kernelH e u a x :=
      integral_congr_ae (ae_of_all _ fun x => by
        dsimp only [kernelH]
        exact integrand_mul_pair _ (fun x => pairH e u (a * absPos x)) e u x)
    have h2 : ∫ x, integrand (𝓕⁻ f : 𝓢(ℝ, ℂ)) e (-u) x * pairK e u (a⁻¹ * absPos x) =
        ∫ x, (𝓕⁻ f : 𝓢(ℝ, ℂ)) x * kernelK e u a⁻¹ x :=
      integral_congr_ae (ae_of_all _ fun x => by
        dsimp only [kernelK]
        exact integrand_mul_pair _ (fun x => pairK e u (a⁻¹ * absPos x)) e (-u) x)
    rw [h1, h2, integral_fourierInv_mul f hK] at h
    rw [h, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    ring
  have hcont : Continuous (fun x => (a : ℂ) * fourierInvInt (kernelK e u a⁻¹) x) :=
    continuous_const.mul (continuous_fourierInvInt hK)
  refine ae_eq_of_integral_contDiff_smul_eq hH.locallyIntegrable hcont.locallyIntegrable
    fun φ hφ hφc => ?_
  have hφ' : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hφc.comp_left (map_zero _)
  set ψ : 𝓢(ℝ, ℂ) := hφ'.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hφ) with hψ
  have hψx : ∀ x, ψ x = (φ x : ℂ) := fun x => Complex.ofRealCLM_apply (φ x)
  have h := key ψ
  simp only [hψx] at h
  simp only [Complex.real_smul]
  exact h


/-! ### The theta identity on `ℝ^n` with independent scalings -/

/-- The inverse Fourier integral on `ℝ^n`: `y ↦ ∫ e^(2π i ⟨x, y⟩) F(x) dx`. -/
def fourierInvN {n : ℕ} (F : (Fin n → ℝ) → ℂ) (y : Fin n → ℝ) : ℂ :=
  ∫ x, Complex.exp (2 * (π : ℂ) * I * ((∑ i, x i * y i : ℝ) : ℂ)) * F x

theorem prod_exp_eq {n : ℕ} (x y : Fin n → ℝ) :
    ∏ i, Complex.exp (2 * (π : ℂ) * I * ((x i * y i : ℝ) : ℂ)) =
      Complex.exp (2 * (π : ℂ) * I * ((∑ i, x i * y i : ℝ) : ℂ)) := by
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]

theorem measurable_kernelK (e : Fin 2) (u : ℂ) (b : ℝ) : Measurable (kernelK e u b) :=
  measurable_integrand ((measurable_pairK e u).comp (measurable_const.mul measurable_absPos)) e (-u)

theorem kernelH_prod_ae_eq {n : ℕ} (e : Fin n → Fin 2) (u : Fin n → ℂ) {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) :
    (fun x : Fin n → ℝ => ∏ i, kernelH (e i) (u i) (a i) (x i)) =ᵐ[volume]
      fun x => ∏ i, ((a i : ℂ) * fourierInvInt (kernelK (e i) (u i) (a i)⁻¹) (x i)) := by
  have h : ∀ i, ∀ᵐ x : Fin n → ℝ ∂volume, kernelH (e i) (u i) (a i) (x i) =
      (a i : ℂ) * fourierInvInt (kernelK (e i) (u i) (a i)⁻¹) (x i) := fun i =>
    (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => (volume : Measure ℝ)) (i := i)).eventually
      (kernelH_ae_eq (e i) (u i) (ha i))
  filter_upwards [ae_all_iff.2 h] with x hx
  exact Finset.prod_congr rfl fun i _ => hx i

/-- Fubini for the inverse Fourier integral on `ℝ^n`:
`∫ F(x) ∏ᵢ Ǩ_i(x_i) dx = ∫ F̌(y) ∏ᵢ K_i(y_i) dy` for integrable `F` and `K_i`. -/
theorem integral_mul_prod_fourierInvInt {n : ℕ} {F : (Fin n → ℝ) → ℂ} (hF : Integrable F)
    {K : Fin n → ℝ → ℂ} (hK : ∀ i, Integrable (K i)) (hKm : ∀ i, Measurable (K i)) :
    ∫ x, F x * ∏ i, fourierInvInt (K i) (x i) = ∫ y, fourierInvN F y * ∏ i, K i (y i) := by
  have hprod : Integrable (fun y : Fin n → ℝ => ∏ i, K i (y i)) :=
    Integrable.fintype_prod (μ := fun _ => volume) hK
  have hm : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      ∏ i, (Complex.exp (2 * (π : ℂ) * I * ((p.1 i * p.2 i : ℝ) : ℂ)) * K i (p.2 i))) := by
    refine Finset.measurable_prod _ fun i _ => ?_
    have hc : Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        Complex.exp (2 * (π : ℂ) * I * ((p.1 i * p.2 i : ℝ) : ℂ))) := by fun_prop
    exact hc.measurable.mul ((hKm i).comp ((measurable_pi_apply i).comp measurable_snd))
  have hG : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => F p.1 *
      ∏ i, (Complex.exp (2 * (π : ℂ) * I * ((p.1 i * p.2 i : ℝ) : ℂ)) * K i (p.2 i)))
      (volume.prod volume) := by
    refine (hF.mul_prod hprod).norm.mono'
      (hF.aestronglyMeasurable.comp_fst.mul hm.aestronglyMeasurable) (ae_of_all _ fun p => ?_)
    simp only [norm_mul, norm_prod, norm_exp_two_pi_I_mul', one_mul]
    exact le_rfl
  have h2 : ∫ x, F x * ∏ i, fourierInvInt (K i) (x i) = ∫ x, ∫ y : Fin n → ℝ, F x *
      ∏ i, (Complex.exp (2 * (π : ℂ) * I * ((x i * y i : ℝ) : ℂ)) * K i (y i)) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [integral_const_mul]
    congr 1
    unfold fourierInvInt
    exact (integral_fintype_prod_volume_eq_prod
      (fun i (y : ℝ) => Complex.exp (2 * (π : ℂ) * I * ((x i * y : ℝ) : ℂ)) * K i y)).symm
  rw [h2, integral_integral_swap hG]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  dsimp only
  unfold fourierInvN
  rw [← integral_mul_const]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  dsimp only
  rw [Finset.prod_mul_distrib, prod_exp_eq]
  ring

/-- The theta identity on `ℝ^n` with independent scalings `a_i > 0`: for integrable `F`,
`∫ F(x) ∏ᵢ H_i(x_i) dx = (∏ᵢ a_i) ∫ F̌(y) ∏ᵢ K_i(y_i) dy`, where
`H_i(x) = sgn(x)^(e_i) |x|^(u_i - 1) h_i(a_i |x|)`,
`K_i(y) = sgn(y)^(e_i) |y|^(-u_i - 1) k_i(a_i⁻¹ |y|)` and `F̌` is the inverse Fourier integral. -/
theorem torus_theta_identity {n : ℕ} (e : Fin n → Fin 2) (u : Fin n → ℂ) {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) {F : (Fin n → ℝ) → ℂ} (hF : Integrable F) :
    ∫ x, F x * ∏ i, kernelH (e i) (u i) (a i) (x i) =
      (∏ i, (a i : ℂ)) * ∫ y, fourierInvN F y * ∏ i, kernelK (e i) (u i) (a i)⁻¹ (y i) := by
  have h1 : ∫ x, F x * ∏ i, kernelH (e i) (u i) (a i) (x i) =
      (∏ i, (a i : ℂ)) *
        ∫ x, F x * ∏ i, fourierInvInt (kernelK (e i) (u i) (a i)⁻¹) (x i) := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [kernelH_prod_ae_eq e u ha] with x hx
    rw [hx, Finset.prod_mul_distrib]
    ring
  rw [h1, integral_mul_prod_fourierInvInt (K := fun i => kernelK (e i) (u i) (a i)⁻¹) hF
    (fun i => integrable_kernel (measurable_pairK _ _) (rapidDecay_pairK _ _)
      (inv_pos.2 (ha i)) _ _)
    (fun i => measurable_kernelK _ _ _)]

end Langlands.Global.RankinSelbergGlobal.ArchimedeanTateTheta

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.LocalFactor.RealTate ArchimedeanMellinPair ArchimedeanTateTheta

/-- The real Tate theta identity for the explicit inverse Mellin pair, and its tensor product
on `ℝ^n` with independent positive scalings. -/
def ArchimedeanTateThetaStatement : Prop :=
  (∀ (f : 𝓢(ℝ, ℂ)) (e : Fin 2) (u : ℂ) (a : ℝ), 0 < a →
    theta volume (integrand f e u) absPos (pairH e u) a =
      (a : ℂ) * theta volume (integrand (𝓕⁻ f : 𝓢(ℝ, ℂ)) e (-u)) absPos (pairK e u) a⁻¹) ∧
  (∀ (n : ℕ) (e : Fin n → Fin 2) (u : Fin n → ℂ) (a : Fin n → ℝ) (F : (Fin n → ℝ) → ℂ),
    (∀ i, 0 < a i) → Integrable F →
      (∫ x, F x * ∏ i, kernelH (e i) (u i) (a i) (x i)) =
        (∏ i, (a i : ℂ)) * ∫ y, fourierInvN F y * ∏ i, kernelK (e i) (u i) (a i)⁻¹ (y i))

theorem archimedeanTateTheta : ArchimedeanTateThetaStatement :=
  ⟨fun f e u _ ha => theta_identity f e u ha,
    fun _ e u _ _ ha hF => torus_theta_identity e u ha hF⟩

end Langlands.Global.RankinSelbergGlobal
