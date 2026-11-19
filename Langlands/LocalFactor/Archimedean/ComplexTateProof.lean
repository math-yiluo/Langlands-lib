import Langlands.LocalFactor.Archimedean.ComplexTateGaussian
import Langlands.LocalFactor.Archimedean.ComplexTateIdentity
import Langlands.LocalFactor.Archimedean.RealTateProof

/-! # The complex local Tate functional equation -/

noncomputable section

open Complex Filter Set
open scoped SchwartzMap Topology

namespace Langlands.LocalFactor.ComplexTate

private def shift (m : ℤ) : ℂ := (m.natAbs : ℂ) / 2

private theorem re_add_shift_pos {u : ℂ} (hu : 0 < u.re) (m : ℤ) :
    0 < (u + shift m).re := by
  simp only [shift, add_re, div_ofNat_re, natCast_re]
  positivity

private theorem re_one_sub_pos {u : ℂ} (hu : u.re < 1) : 0 < (1 - u).re := by
  rw [sub_re, one_re]
  exact sub_pos.mpr hu

private theorem gamma_ne_zero {u : ℂ} (hu : 0 < u.re) : Gammaℂ u ≠ 0 := by
  rw [Gammaℂ_def]
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  exact mul_ne_zero (mul_ne_zero two_ne_zero (cpow_ne_zero_iff.mpr (Or.inl hπ)))
    (Gamma_ne_zero_of_re_pos hu)

private theorem meromorphicAt_Gammaℂ (u : ℂ) : MeromorphicAt Gammaℂ u := by
  have h : AnalyticAt ℂ (fun w => (Gammaℂ w)⁻¹) u := differentiable_Gammaℂ_inv.analyticAt u
  exact h.meromorphicAt.inv.congr (Eventually.of_forall fun w => inv_inv (Gammaℂ w))

/-! ## The functional equation on the common strip -/

private theorem zeta_fourier_mul_Gammaℂ (f : 𝓢(ℂ, ℂ)) (m : ℤ) {u : ℂ}
    (hu0 : 0 < u.re) (hu1 : u.re < 1) :
    zeta (fourier f) (-m) (1 - u) * Gammaℂ (u + shift m) =
      I ^ m.natAbs * Gammaℂ (1 - u + shift m) * zeta f m u := by
  have hg : (gaussSchwartz m : ℂ → ℂ) = gaussian m := funext (gaussSchwartz_apply m)
  have hfg : (fourier (gaussSchwartz m) : ℂ → ℂ) =
      fun y => I ^ m.natAbs * gaussian (-m) y := by
    funext y
    simpa only [fourier_apply, hg, traceChar] using integral_exp_mul_gaussian m y
  have h := tate_identity f (gaussSchwartz m) m hu0 hu1
  simp only [hg, hfg, zeta_const_mul, zeta_gaussian m hu0,
    zeta_gaussian (-m) (re_one_sub_pos hu1), Int.natAbs_neg] at h
  unfold shift
  linear_combination -h

/-! ## Meromorphic continuation -/

/-- The reflected formula for the continuation on `Re u < 1`. -/
private def reflectedZeta (f : 𝓢(ℂ, ℂ)) (m : ℤ) (u : ℂ) : ℂ :=
  zeta (fourier f) (-m) (1 - u) * Gammaℂ (u + shift m) /
    (I ^ m.natAbs * Gammaℂ (1 - u + shift m))

private theorem zeta_eq_reflectedZeta (f : 𝓢(ℂ, ℂ)) (m : ℤ) {u : ℂ}
    (hu0 : 0 < u.re) (hu1 : u.re < 1) : zeta f m u = reflectedZeta f m u := by
  have hΓ := gamma_ne_zero (re_add_shift_pos (re_one_sub_pos hu1) m)
  have hI := pow_ne_zero m.natAbs I_ne_zero
  rw [reflectedZeta, zeta_fourier_mul_Gammaℂ f m hu0 hu1, eq_div_iff (mul_ne_zero hI hΓ)]
  ring

private theorem meromorphicAt_reflectedZeta (f : 𝓢(ℂ, ℂ)) (m : ℤ) {u : ℂ} (hu : u.re < 1) :
    MeromorphicAt (reflectedZeta f m) u := by
  have hz : AnalyticAt ℂ (fun w => zeta (fourier f) (-m) (1 - w)) u :=
    AnalyticAt.comp (g := zeta (fourier f) (-m)) (f := fun w : ℂ => 1 - w)
      (analyticAt_zeta (fourier f) (-m) (re_one_sub_pos hu)) (by fun_prop)
  have hΓ : MeromorphicAt (fun w => Gammaℂ (w + shift m)) u :=
    (meromorphicAt_Gammaℂ _).comp_analyticAt (g := fun w : ℂ => w + shift m) (by fun_prop)
  have hΓ' : MeromorphicAt (fun w => Gammaℂ (1 - w + shift m)) u :=
    (meromorphicAt_Gammaℂ _).comp_analyticAt (g := fun w : ℂ => 1 - w + shift m) (by fun_prop)
  exact (hz.meromorphicAt.mul hΓ).div ((MeromorphicAt.const (I ^ m.natAbs) u).mul hΓ')

private def gluedZeta (f : 𝓢(ℂ, ℂ)) (m : ℤ) (u : ℂ) : ℂ :=
  if 0 < u.re then zeta f m u else reflectedZeta f m u

private theorem meromorphicAt_gluedZeta (f : 𝓢(ℂ, ℂ)) (m : ℤ) (u : ℂ) :
    MeromorphicAt (gluedZeta f m) u := by
  by_cases hu : 0 < u.re
  · have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re
    have hev : zeta f m =ᶠ[𝓝 u] gluedZeta f m := by
      filter_upwards [hopen.mem_nhds hu] with w hw
      exact (ite_eq_left (show 0 < w.re from hw)).symm
    exact (analyticAt_zeta f m hu).meromorphicAt.congr (hev.filter_mono nhdsWithin_le_nhds)
  · have hu1 : u.re < 1 := by linarith [not_lt.mp hu]
    have hopen : IsOpen {w : ℂ | w.re < 1} := isOpen_lt continuous_re continuous_const
    have hev : reflectedZeta f m =ᶠ[𝓝 u] gluedZeta f m := by
      filter_upwards [hopen.mem_nhds hu1] with w hw
      unfold gluedZeta
      split_ifs with hw0
      · exact (zeta_eq_reflectedZeta f m hw0 hw).symm
      · rfl
    exact (meromorphicAt_reflectedZeta f m hu1).congr (hev.filter_mono nhdsWithin_le_nhds)

private def extendsIntegral (Z : ℂ → ℂ) (f : 𝓢(ℂ, ℂ)) (m : ℤ) (t : ℂ) : Prop :=
  MeromorphicNFOn Z univ ∧ ∀ s, 0 < (s + t).re → Z s = zeta f m (s + t)

/-- The meromorphic normal form of the glued zeta function in the variable `s = u - t`. -/
private def extension (f : 𝓢(ℂ, ℂ)) (m : ℤ) (t : ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (fun s => gluedZeta f m (s + t)) univ

private theorem extension_spec (f : 𝓢(ℂ, ℂ)) (m : ℤ) (t : ℂ) :
    extendsIntegral (extension f m t) f m t := by
  refine ⟨meromorphicNFOn_toMeromorphicNFOn _ _, fun s hs => ?_⟩
  have hm : MeromorphicOn (fun w => gluedZeta f m (w + t)) univ := fun w _ =>
    (meromorphicAt_gluedZeta f m (w + t)).comp_analyticAt (g := fun v : ℂ => v + t) (by fun_prop)
  have hev : (fun w => zeta f m (w + t)) =ᶠ[𝓝 s] fun w => gluedZeta f m (w + t) := by
    filter_upwards [(RealTate.isOpen_re_add_pos t).mem_nhds hs] with w hw
    exact (ite_eq_left (show 0 < (w + t).re from hw)).symm
  have ha : AnalyticAt ℂ (fun w => gluedZeta f m (w + t)) s :=
    (AnalyticAt.comp (g := zeta f m) (f := fun w : ℂ => w + t)
      (analyticAt_zeta f m hs) (by fun_prop)).congr hev
  rw [extension, toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ s),
    toMeromorphicNFAt_eq_self.2 ha.meromorphicNFAt]
  exact ite_eq_left hs

private theorem extension_unique (f : 𝓢(ℂ, ℂ)) (m : ℤ) (t : ℂ) {Z Y : ℂ → ℂ}
    (hZ : extendsIntegral Z f m t) (hY : extendsIntegral Y f m t) : Z = Y :=
  RealTate.eq_of_meromorphicNFOn hZ.1 hY.1 (RealTate.isOpen_re_add_pos t)
    (x := 1 - t) (by simp) fun s hs => (hZ.2 s hs).trans (hY.2 s hs).symm

/-! ## The scaled functional equation -/

private theorem functional_equation (f : 𝓢(ℂ, ℂ)) (m : ℤ) (t : ℂ) (a : ℂˣ) (c : NNReal)
    {Z Y : ℂ → ℂ} (hZ : extendsIntegral Z f m t)
    (hY : extendsIntegral Y (scaledFourier a c f) (-m) (-t)) (s₀ : ℂ) :
    (fun s => Y (1 - s) / Gammaℂ (1 - s - t + shift m)) =ᶠ[𝓝[≠] s₀]
      (fun s => (c : ℂ) * direction (a : ℂ) ^ m *
        (‖(a : ℂ)‖ : ℂ) ^ (2 * (s + t - 1)) * I ^ m.natAbs *
        (Z s / Gammaℂ (s + t + shift m))) := by
  have hF : MeromorphicOn (fun s => Y (1 - s) / Gammaℂ (1 - s - t + shift m)) univ :=
    fun s _ =>
      ((hY.1.meromorphicOn (1 - s) (mem_univ _)).comp_analyticAt (g := fun s : ℂ => 1 - s)
        (by fun_prop)).div
        ((meromorphicAt_Gammaℂ _).comp_analyticAt (g := fun s : ℂ => 1 - s - t + shift m)
          (by fun_prop))
  have hG : MeromorphicOn (fun s => (c : ℂ) * direction (a : ℂ) ^ m *
      (‖(a : ℂ)‖ : ℂ) ^ (2 * (s + t - 1)) * I ^ m.natAbs *
        (Z s / Gammaℂ (s + t + shift m))) univ := fun s _ => by
    have hcp : AnalyticAt ℂ (fun w : ℂ => (‖(a : ℂ)‖ : ℂ) ^ (2 * (w + t - 1))) s :=
      analyticAt_const.cpow (by fun_prop) (ofReal_mem_slitPlane.2 (norm_pos_iff.mpr a.ne_zero))
    exact (((MeromorphicAt.const _ s).mul hcp.meromorphicAt).mul
      (MeromorphicAt.const _ s)).mul ((hZ.1.meromorphicOn s (mem_univ _)).div
      ((meromorphicAt_Gammaℂ _).comp_analyticAt (g := fun s : ℂ => s + t + shift m)
        (by fun_prop)))
  have hopen : IsOpen {s : ℂ | 0 < (s + t).re ∧ (s + t).re < 1} :=
    (RealTate.isOpen_re_add_pos t).inter
      (isOpen_lt (continuous_re.comp (continuous_id.add continuous_const)) continuous_const)
  refine RealTate.eventuallyEq_nhdsNE_of_eqOn hF hG hopen (x := 1 / 2 - t)
    ⟨by norm_num, by norm_num⟩ (fun s hs => ?_) s₀
  obtain ⟨hu0, hu1⟩ := hs
  have hy : Y (1 - s) = zeta (scaledFourier a c f) (-m) (1 - (s + t)) := by
    have he : 1 - s + -t = 1 - (s + t) := by ring
    rw [← he]
    apply hY.2
    rw [he]
    exact re_one_sub_pos hu1
  have hΓ := gamma_ne_zero (re_add_shift_pos hu0 m)
  have hΓ' := gamma_ne_zero (re_add_shift_pos (re_one_sub_pos hu1) m)
  have hφ := eq_div_of_mul_eq hΓ (zeta_fourier_mul_Gammaℂ f m hu0 hu1)
  simp only
  rw [hy, hZ.2 s hu0, zeta_scaledFourier, neg_neg, hφ,
    show -2 * (1 - (s + t)) = 2 * (s + t - 1) by ring,
    show 1 - s - t + shift m = 1 - (s + t) + shift m by ring]
  field_simp

/-- Tate's local zeta continuation and normalized functional equation at the complex place. -/
theorem complexArchimedeanTateStatement : ComplexArchimedeanTateStatement := by
  unfold ComplexArchimedeanTateStatement
  dsimp only
  refine ⟨fun f m t s hs => integrable_integrand f m hs, fun f m t => ?_,
    fun f m t a c _ => ?_, ?_⟩
  · exact ⟨extension f m t, extension_spec f m t,
      fun Z hZ => extension_unique f m t hZ (extension_spec f m t)⟩
  · exact ⟨scaledFourier a c f, scaledFourier_apply a c f,
      fun Z Y hZ hY s₀ => functional_equation f m t a c hZ hY s₀⟩
  · intro m
    refine ⟨⟨gaussSchwartz m, gaussSchwartz_apply m⟩, ?_, ?_⟩
    · intro z
      simpa only [one_mul, NNReal.coe_one, ofReal_one, gaussian, measure] using
        integral_exp_mul_gaussian m z
    · intro t s hs
      exact zeta_gaussian m hs

end Langlands.LocalFactor.ComplexTate
