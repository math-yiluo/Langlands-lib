import Langlands.LocalFactor.Archimedean.RealTateIdentity
import Langlands.LocalFactor.Archimedean.RealTateGaussian
import Langlands.LocalFactor.Archimedean.Statement
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! # The real local Tate functional equation

We prove `Langlands.LocalFactor.RealArchimedeanTateStatement`: convergence of the real Tate zeta
integral `Z(f, e, u) = ∫ f(x) sgn(x)^e |x|^(u-1) dx` for `0 < Re u`, its unique continuation to
a function in meromorphic normal form on `ℂ`, the local functional equation for the dilated and
scaled inverse Fourier transform `y ↦ c ∫ exp(2π i a x y) f(x) dx`, and the Gaussian
normalization. The functional equation is first proved on the strip `0 < Re u < 1` from Tate's
identity with the adapted Gaussian as auxiliary function; the continuation to `Re u ≤ 0` is
defined by the resulting formula and both the continuation and the functional equation then
follow from the identity theorem for meromorphic functions. See the paired Markdown.
-/

noncomputable section

open MeasureTheory Filter Set Complex Function
open scoped SchwartzMap FourierTransform Real Topology

namespace Langlands.LocalFactor.RealTate

/-! ### The identity theorem for meromorphic functions on `ℂ` -/

/-- Two functions meromorphic on `ℂ` that agree on a nonempty open set agree on a punctured
neighbourhood of every point. -/
theorem eventuallyEq_nhdsNE_of_eqOn {F G : ℂ → ℂ} (hF : MeromorphicOn F univ)
    (hG : MeromorphicOn G univ) {U : Set ℂ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ U)
    (hFG : EqOn F G U) (s₀ : ℂ) : F =ᶠ[𝓝[≠] s₀] G := by
  have hx' : meromorphicOrderAt (F - G) x = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hx)] with z hz
    simp [hFG hz]
  have h := (hF.sub hG).meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
    (mem_univ x) (mem_univ s₀) hx'
  rw [meromorphicOrderAt_eq_top_iff] at h
  filter_upwards [h] with z hz
  rw [Pi.sub_apply, sub_eq_zero] at hz
  exact hz

/-- Two functions in meromorphic normal form on `ℂ` that agree on a nonempty open set are
equal. -/
theorem eq_of_meromorphicNFOn {F G : ℂ → ℂ} (hF : MeromorphicNFOn F univ)
    (hG : MeromorphicNFOn G univ) {U : Set ℂ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ U)
    (hFG : EqOn F G U) : F = G := by
  funext s₀
  have h := eventuallyEq_nhdsNE_of_eqOn hF.meromorphicOn hG.meromorphicOn hU hx hFG s₀
  exact (((hF (mem_univ s₀)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (hG (mem_univ s₀))).1 h).eq_of_nhds

/-- `Γℝ` is meromorphic at every point, being the inverse of the entire function `1 / Γℝ`. -/
theorem meromorphicAt_Gammaℝ (w : ℂ) : MeromorphicAt Gammaℝ w := by
  have h : AnalyticAt ℂ (fun s => (Gammaℝ s)⁻¹) w := differentiable_Gammaℝ_inv.analyticAt w
  exact h.meromorphicAt.inv.congr (Eventually.of_forall fun s => by simp)

/-! ### The adapted Gaussian -/

/-- The adapted Gaussian `x ↦ x^e exp(-π x²)` of parity `e`. -/
def gaussian (e : Fin 2) (x : ℝ) : ℂ :=
  (x : ℂ) ^ e.val * Complex.exp (-(π : ℂ) * (x : ℂ) ^ 2)

theorem gaussian_eq_realGaussian (e : Fin 2) (x : ℝ) :
    gaussian e x = Langlands.Global.Hecke.realGaussian 1 e.val x := by
  unfold gaussian Langlands.Global.Hecke.realGaussian
  push_cast
  ring_nf

/-- The adapted Gaussian as a Schwartz function. -/
def gaussSchwartzE (e : Fin 2) : 𝓢(ℝ, ℂ) :=
  gaussSchwartz (Polynomial.X ^ e.val)

theorem gaussSchwartzE_apply (e : Fin 2) (x : ℝ) : gaussSchwartzE e x = gaussian e x := by
  rw [gaussSchwartzE, gaussSchwartz_apply, Polynomial.eval_pow, Polynomial.eval_X, gaussian]
  push_cast
  ring

/-- The Gaussian is an eigenfunction of the Fourier transform:
`∫ exp(2π i x y) x^e exp(-π x²) dx = i^e y^e exp(-π y²)`. -/
theorem integral_exp_mul_gaussian (e : Fin 2) (y : ℝ) :
    ∫ x : ℝ, Complex.exp (2 * (π : ℂ) * I * ((x * y : ℝ) : ℂ)) * gaussian e x =
      I ^ e.val * gaussian e y := by
  have hfun : (fun x : ℝ => Complex.exp (2 * (π : ℂ) * I * ((x * y : ℝ) : ℂ)) * gaussian e x) =
      fun x => Langlands.Global.Hecke.realGaussian 1 e.val x * (𝐞 (1 * x * y) : ℂ) := by
    funext x
    rw [gaussian_eq_realGaussian, Real.fourierChar_apply, mul_comm]
    congr 2
    push_cast
    ring
  have h := Langlands.Global.Hecke.integral_realGaussian_mul_fourierChar (a := 1) one_ne_zero e y
  simp only [abs_one] at h
  rw [hfun, h, gaussian_eq_realGaussian]
  simp

/-- The Gaussian zeta integral: `Z(x^e exp(-π x²), e, w) = Γℝ(w + e)` for `0 < Re w`. -/
theorem zeta_gaussian (e : Fin 2) {w : ℂ} (hw : 0 < w.re) :
    zeta (gaussian e) e w = Gammaℝ (w + e.val) := by
  have hpos : 0 < (w + 0 + (e.val : ℂ)).re := by
    simp only [add_zero, add_re, natCast_re]
    have : (0 : ℝ) ≤ (e.val : ℝ) := Nat.cast_nonneg _
    linarith
  have h := Langlands.Global.Hecke.integral_realGaussian_mul_realCharFun one_pos e.val 0 w hpos
  calc zeta (gaussian e) e w = ∫ x : ℝ, Langlands.Global.Hecke.realGaussian 1 e.val x *
        Langlands.Global.Hecke.realCharFun e.val 0 x * ((|x| : ℝ) : ℂ) ^ (w - 1) := by
        refine integral_congr_ae ?_
        filter_upwards [Measure.ae_ne volume 0] with x hx
        simp only [integrand, hx, ↓reduceIte, Langlands.Global.Hecke.realCharFun, cpow_zero,
          mul_one, gaussian_eq_realGaussian]
    _ = Gammaℝ (w + e.val) := by
        rw [h]
        simp

theorem zeta_gaussSchwartzE (e : Fin 2) {w : ℂ} (hw : 0 < w.re) :
    zeta (gaussSchwartzE e) e w = Gammaℝ (w + e.val) := by
  have hg : (gaussSchwartzE e : ℝ → ℂ) = gaussian e := funext (gaussSchwartzE_apply e)
  rw [hg, zeta_gaussian e hw]

theorem fourierInv_gaussSchwartzE (e : Fin 2) (y : ℝ) :
    (𝓕⁻ (gaussSchwartzE e) : 𝓢(ℝ, ℂ)) y = I ^ e.val * gaussSchwartzE e y := by
  rw [fourierInv_apply_real]
  simp_rw [gaussSchwartzE_apply]
  exact integral_exp_mul_gaussian e y

theorem zeta_fourierInv_gaussSchwartzE (e : Fin 2) {w : ℂ} (hw : 0 < w.re) :
    zeta (𝓕⁻ (gaussSchwartzE e) : 𝓢(ℝ, ℂ)) e w = I ^ e.val * Gammaℝ (w + e.val) := by
  have h : ((𝓕⁻ (gaussSchwartzE e) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = fun y => I ^ e.val * gaussian e y := by
    funext y
    rw [fourierInv_gaussSchwartzE, gaussSchwartzE_apply]
  rw [h, zeta_const_mul, zeta_gaussian e hw]

/-! ### The functional equation on the critical strip -/

/-- The functional equation on `0 < Re u < 1`:
`Z(f̂, e, 1 - u) Γℝ(u + e) = i^e Γℝ(1 - u + e) Z(f, e, u)` with `f̂ = 𝓕⁻ f`. -/
theorem zeta_fourierInv_mul_Gammaℝ (f : 𝓢(ℝ, ℂ)) (e : Fin 2) {u : ℂ} (hu0 : 0 < u.re)
    (hu1 : u.re < 1) :
    zeta (𝓕⁻ f : 𝓢(ℝ, ℂ)) e (1 - u) * Gammaℝ (u + e.val) =
      I ^ e.val * Gammaℝ (1 - u + e.val) * zeta f e u := by
  have h := tate_identity f (gaussSchwartzE e) e hu0 hu1
  have h1 : 0 < (1 - u).re := by simp only [sub_re, one_re]; linarith
  rw [zeta_fourierInv_gaussSchwartzE e h1, zeta_gaussSchwartzE e hu0] at h
  linear_combination -h

/-- The continuation formula `Z(f̂, e, 1 - u) Γℝ(u + e) / (i^e Γℝ(1 - u + e))`. -/
def contFormula (f : 𝓢(ℝ, ℂ)) (e : Fin 2) (u : ℂ) : ℂ :=
  zeta (𝓕⁻ f : 𝓢(ℝ, ℂ)) e (1 - u) * Gammaℝ (u + e.val) / (I ^ e.val * Gammaℝ (1 - u + e.val))

theorem re_one_sub_add_pos {u : ℂ} (hu1 : u.re < 1) (e : Fin 2) :
    0 < (1 - u + (e.val : ℂ)).re := by
  simp only [add_re, sub_re, one_re, natCast_re]
  have : (0 : ℝ) ≤ (e.val : ℝ) := Nat.cast_nonneg _
  linarith

theorem re_add_pos {u : ℂ} (hu0 : 0 < u.re) (e : Fin 2) : 0 < (u + (e.val : ℂ)).re := by
  simp only [add_re, natCast_re]
  have : (0 : ℝ) ≤ (e.val : ℝ) := Nat.cast_nonneg _
  linarith

theorem zeta_eq_contFormula (f : 𝓢(ℝ, ℂ)) (e : Fin 2) {u : ℂ} (hu0 : 0 < u.re)
    (hu1 : u.re < 1) : zeta f e u = contFormula f e u := by
  have hΓ := Gammaℝ_ne_zero_of_re_pos (re_one_sub_add_pos hu1 e)
  have hI : I ^ e.val ≠ 0 := pow_ne_zero _ I_ne_zero
  rw [contFormula, zeta_fourierInv_mul_Gammaℝ f e hu0 hu1, eq_div_iff (mul_ne_zero hI hΓ)]
  ring

/-! ### Meromorphic continuation -/

/-- The glued function: `Z(f, e, u)` for `0 < Re u` and the continuation formula otherwise. -/
def contZeta (f : 𝓢(ℝ, ℂ)) (e : Fin 2) (u : ℂ) : ℂ :=
  if 0 < u.re then zeta f e u else contFormula f e u

theorem meromorphicAt_contFormula (f : 𝓢(ℝ, ℂ)) (e : Fin 2) {u : ℂ} (hu : u.re < 1) :
    MeromorphicAt (contFormula f e) u := by
  have h0 : 0 < (1 - u).re := by simp only [sub_re, one_re]; linarith
  have h1 : AnalyticAt ℂ (fun w => zeta (𝓕⁻ f : 𝓢(ℝ, ℂ)) e (1 - w)) u :=
    AnalyticAt.comp (g := zeta (𝓕⁻ f : 𝓢(ℝ, ℂ)) e) (f := fun w : ℂ => 1 - w)
      (analyticAt_zeta (𝓕⁻ f) e h0) (by fun_prop)
  have h2 : MeromorphicAt (fun w => Gammaℝ (w + e.val)) u :=
    (meromorphicAt_Gammaℝ _).comp_analyticAt (g := fun w : ℂ => w + e.val) (by fun_prop)
  have h3 : MeromorphicAt (fun w => Gammaℝ (1 - w + e.val)) u :=
    (meromorphicAt_Gammaℝ _).comp_analyticAt (g := fun w : ℂ => 1 - w + e.val) (by fun_prop)
  exact (h1.meromorphicAt.mul h2).div ((MeromorphicAt.const (I ^ e.val) u).mul h3)

theorem meromorphicAt_contZeta (f : 𝓢(ℝ, ℂ)) (e : Fin 2) (u : ℂ) :
    MeromorphicAt (contZeta f e) u := by
  by_cases hu : 0 < u.re
  · have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : zeta f e =ᶠ[𝓝 u] contZeta f e := by
      filter_upwards [hopen.mem_nhds hu] with w hw
      have hw' : 0 < w.re := hw
      simp only [contZeta, hw', ↓reduceIte]
    exact (analyticAt_zeta f e hu).meromorphicAt.congr (hev.filter_mono nhdsWithin_le_nhds)
  · have hu1 : u.re < 1 := by linarith [not_lt.mp hu]
    have hopen : IsOpen {w : ℂ | w.re < 1} := isOpen_lt Complex.continuous_re continuous_const
    have hev : contFormula f e =ᶠ[𝓝 u] contZeta f e := by
      filter_upwards [hopen.mem_nhds hu1] with w hw
      have hw' : w.re < 1 := hw
      simp only [contZeta]
      split_ifs with h
      · exact (zeta_eq_contFormula f e h hw').symm
      · rfl
    exact (meromorphicAt_contFormula f e hu1).congr (hev.filter_mono nhdsWithin_le_nhds)

theorem meromorphicOn_contZeta_add (f : 𝓢(ℝ, ℂ)) (e : Fin 2) (t : ℂ) :
    MeromorphicOn (fun s => contZeta f e (s + t)) univ := fun s _ =>
  (meromorphicAt_contZeta f e (s + t)).comp_analyticAt (g := fun s : ℂ => s + t) (by fun_prop)

/-- The continuation of `s ↦ Z(f, e, s + t)`: the meromorphic normal form of the glued
function. -/
def contZetaNF (f : 𝓢(ℝ, ℂ)) (e : Fin 2) (t : ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (fun s => contZeta f e (s + t)) univ

theorem isOpen_re_add_pos (t : ℂ) : IsOpen {s : ℂ | 0 < (s + t).re} :=
  isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_id.add continuous_const))

theorem contZetaNF_spec (f : 𝓢(ℝ, ℂ)) (e : Fin 2) (t : ℂ) :
    MeromorphicNFOn (contZetaNF f e t) univ ∧
      ∀ s, 0 < (s + t).re → contZetaNF f e t s = zeta f e (s + t) := by
  refine ⟨meromorphicNFOn_toMeromorphicNFOn _ _, fun s hs => ?_⟩
  have hev : (fun w => zeta f e (w + t)) =ᶠ[𝓝 s] fun w => contZeta f e (w + t) := by
    filter_upwards [(isOpen_re_add_pos t).mem_nhds hs] with w hw
    have hw' : 0 < (w + t).re := hw
    simp only [contZeta, hw', ↓reduceIte]
  have han : AnalyticAt ℂ (fun w => contZeta f e (w + t)) s :=
    (AnalyticAt.comp (g := zeta f e) (f := fun w : ℂ => w + t) (analyticAt_zeta f e hs)
      (by fun_prop)).congr hev
  rw [contZetaNF, toMeromorphicNFOn_eq_toMeromorphicNFAt (meromorphicOn_contZeta_add f e t)
    (mem_univ s), toMeromorphicNFAt_eq_self.2 han.meromorphicNFAt]
  simp only [contZeta, hs, ↓reduceIte]

theorem extension_unique (f : 𝓢(ℝ, ℂ)) (e : Fin 2) (t : ℂ) {Z Z' : ℂ → ℂ}
    (hZ : MeromorphicNFOn Z univ ∧ ∀ s, 0 < (s + t).re → Z s = zeta f e (s + t))
    (hZ' : MeromorphicNFOn Z' univ ∧ ∀ s, 0 < (s + t).re → Z' s = zeta f e (s + t)) :
    Z = Z' :=
  eq_of_meromorphicNFOn hZ.1 hZ'.1 (isOpen_re_add_pos t) (x := 1 - t) (by simp)
    fun s hs => by rw [hZ.2 s hs, hZ'.2 s hs]

/-! ### The dilated and scaled inverse Fourier transform -/

/-- The Schwartz function `y ↦ c (𝓕⁻ f)(a y)`. -/
def dilatedFourierInv (f : 𝓢(ℝ, ℂ)) (a : ℝˣ) (c : ℂ) : 𝓢(ℝ, ℂ) :=
  c • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.unitsEquivAut ℝ a)
    (𝓕⁻ f : 𝓢(ℝ, ℂ))

theorem dilatedFourierInv_apply (f : 𝓢(ℝ, ℂ)) (a : ℝˣ) (c : ℂ) (y : ℝ) :
    dilatedFourierInv f a c y = c * (𝓕⁻ f : 𝓢(ℝ, ℂ)) ((a : ℝ) * y) := by
  change c • (𝓕⁻ f : 𝓢(ℝ, ℂ)) (ContinuousLinearEquiv.unitsEquivAut ℝ a y) = _
  rw [ContinuousLinearEquiv.unitsEquivAut_apply, smul_eq_mul, mul_comm y]

theorem dilatedFourierInv_eq (f : 𝓢(ℝ, ℂ)) (a : ℝˣ) (c : ℂ) (y : ℝ) :
    dilatedFourierInv f a c y =
      c * ∫ x : ℝ, Complex.exp (2 * (π : ℂ) * I * (((a : ℝ) * x * y : ℝ) : ℂ)) * f x := by
  rw [dilatedFourierInv_apply, fourierInv_apply_real]
  congr 2
  funext x
  rw [show (a : ℝ) * x * y = x * ((a : ℝ) * y) by ring]

/-- Dilation and scaling of the zeta integral:
`Z(c (𝓕⁻ f)(a ·), e, w) = c sgn(a)^e |a|^(-w) Z(𝓕⁻ f, e, w)`. -/
theorem zeta_dilatedFourierInv (f : 𝓢(ℝ, ℂ)) (a : ℝˣ) (c : ℂ) (e : Fin 2) (w : ℂ) :
    zeta (dilatedFourierInv f a c) e w = c * (((a : ℝ) / |(a : ℝ)| : ℝ) : ℂ) ^ e.val *
      ((|(a : ℝ)| : ℝ) : ℂ) ^ (-w) * zeta (𝓕⁻ f : 𝓢(ℝ, ℂ)) e w := by
  have ha : (a : ℝ) ≠ 0 := a.ne_zero
  have hg : (dilatedFourierInv f a c : ℝ → ℂ) =
      fun y => c * (fun y => (𝓕⁻ f : 𝓢(ℝ, ℂ)) ((a : ℝ) * y)) y :=
    funext (dilatedFourierInv_apply f a c)
  have hd := zeta_eq_sign_mul_zeta_comp_mul (𝓕⁻ f : 𝓢(ℝ, ℂ)) e w ha
  rw [hg, zeta_const_mul, hd]
  have hS := sign_pow_mul_sign_pow ha e
  have hA : ((|(a : ℝ)| : ℝ) : ℂ) ^ (-w) * ((|(a : ℝ)| : ℝ) : ℂ) ^ w = 1 := by
    rw [← cpow_add _ _ (abs_cpow_ne_zero ha), neg_add_cancel, cpow_zero]
  set Zd := zeta (fun y => (𝓕⁻ f : 𝓢(ℝ, ℂ)) ((a : ℝ) * y)) e w
  set S := (((a : ℝ) / |(a : ℝ)| : ℝ) : ℂ) ^ e.val
  linear_combination (-c * Zd) * hS + (-c * Zd * S * S) * hA

/-! ### The local functional equation -/

/-- The local functional equation, as an equality of punctured germs at every point. -/
theorem functional_equation (f : 𝓢(ℝ, ℂ)) (e : Fin 2) (t : ℂ) (a : ℝˣ) (c : ℂ) {Z Y : ℂ → ℂ}
    (hZ : MeromorphicNFOn Z univ ∧ ∀ s, 0 < (s + t).re → Z s = zeta f e (s + t))
    (hY : MeromorphicNFOn Y univ ∧
      ∀ s, 0 < (s + -t).re → Y s = zeta (dilatedFourierInv f a c) e (s + -t))
    (s₀ : ℂ) :
    (fun s => Y (1 - s) / Gammaℝ (1 - s - t + e.val)) =ᶠ[𝓝[≠] s₀]
      (fun s => c * (((a : ℝ) / |(a : ℝ)| : ℝ) : ℂ) ^ e.val *
        ((|(a : ℝ)| : ℝ) : ℂ) ^ (s + t - 1) * I ^ e.val *
        (Z s / Gammaℝ (s + t + e.val))) := by
  have hA0 : 0 < |(a : ℝ)| := abs_pos.mpr a.ne_zero
  have hF : MeromorphicOn (fun s => Y (1 - s) / Gammaℝ (1 - s - t + e.val)) univ := fun s _ =>
    ((hY.1.meromorphicOn (1 - s) (mem_univ _)).comp_analyticAt (g := fun s : ℂ => 1 - s)
      (by fun_prop)).div
      ((meromorphicAt_Gammaℝ _).comp_analyticAt (g := fun s : ℂ => 1 - s - t + e.val)
        (by fun_prop))
  have hG : MeromorphicOn (fun s => c * (((a : ℝ) / |(a : ℝ)| : ℝ) : ℂ) ^ e.val *
      ((|(a : ℝ)| : ℝ) : ℂ) ^ (s + t - 1) * I ^ e.val * (Z s / Gammaℝ (s + t + e.val)))
      univ := fun s _ => by
    have hcp : AnalyticAt ℂ (fun s : ℂ => ((|(a : ℝ)| : ℝ) : ℂ) ^ (s + t - 1)) s :=
      analyticAt_const.cpow (by fun_prop) (ofReal_mem_slitPlane.2 hA0)
    exact ((((MeromorphicAt.const _ s).mul hcp.meromorphicAt).mul
      (MeromorphicAt.const _ s))).mul ((hZ.1.meromorphicOn s (mem_univ _)).div
      ((meromorphicAt_Gammaℝ _).comp_analyticAt (g := fun s : ℂ => s + t + e.val)
        (by fun_prop)))
  have hopen : IsOpen {s : ℂ | 0 < (s + t).re ∧ (s + t).re < 1} :=
    (isOpen_re_add_pos t).inter
      (isOpen_lt (Complex.continuous_re.comp (continuous_id.add continuous_const))
        continuous_const)
  refine eventuallyEq_nhdsNE_of_eqOn hF hG hopen (x := 1 / 2 - t) ⟨by norm_num, by norm_num⟩
    (fun s hs => ?_) s₀
  obtain ⟨h0, h1⟩ := hs
  have hY' : Y (1 - s) = zeta (dilatedFourierInv f a c) e (1 - (s + t)) := by
    rw [hY.2 (1 - s) (by
      rw [show 1 - s + -t = 1 - (s + t) by ring]
      simp only [sub_re, one_re]
      linarith), show 1 - s + -t = 1 - (s + t) by ring]
  have key := zeta_fourierInv_mul_Gammaℝ f e h0 h1
  have hΓu := Gammaℝ_ne_zero_of_re_pos (re_add_pos h0 e)
  have hΓ1 := Gammaℝ_ne_zero_of_re_pos (re_one_sub_add_pos h1 e)
  have hφ : zeta (𝓕⁻ f : 𝓢(ℝ, ℂ)) e (1 - (s + t)) =
      I ^ e.val * Gammaℝ (1 - (s + t) + e.val) * zeta f e (s + t) / Gammaℝ (s + t + e.val) :=
    eq_div_of_mul_eq hΓu key
  simp only
  rw [hY', hZ.2 s h0, zeta_dilatedFourierInv, hφ, show -(1 - (s + t)) = s + t - 1 by ring,
    show 1 - s - t + (e.val : ℂ) = 1 - (s + t) + e.val by ring]
  field_simp

/-! ### The Library statement -/

/-- **Tate's local theory at the real place**: `RealArchimedeanTateStatement` holds. -/
theorem realArchimedeanTateStatement : RealArchimedeanTateStatement := by
  unfold RealArchimedeanTateStatement
  intro integrand' zeta' extendsIntegral ft gaussian'
  refine ⟨fun f e t s hs => integrable_integrand f e hs, fun f e t => ?_,
    fun f e t a c _ => ?_, fun e => ⟨?_, fun x => ?_, fun t s hs => ?_⟩⟩
  · exact ⟨contZetaNF f e t, contZetaNF_spec f e t,
      fun Z hZ => extension_unique f e t hZ (contZetaNF_spec f e t)⟩
  · exact ⟨dilatedFourierInv f a (c : ℂ), fun y => dilatedFourierInv_eq f a c y,
      fun Z Y hZ hY s₀ => functional_equation f e t a c hZ hY s₀⟩
  · exact ⟨gaussSchwartzE e, gaussSchwartzE_apply e⟩
  · show ((1 : NNReal) : ℂ) * ∫ y : ℝ,
      Complex.exp (2 * (π : ℂ) * I * ((1 * y * x : ℝ) : ℂ)) * gaussian e y =
        I ^ e.val * gaussian e x
    simp only [one_mul, NNReal.coe_one, ofReal_one]
    exact integral_exp_mul_gaussian e x
  · exact zeta_gaussian e hs

end Langlands.LocalFactor.RealTate
