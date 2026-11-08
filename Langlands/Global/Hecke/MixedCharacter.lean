import Langlands.Global.Hecke.MixedSpaceFourier
import Langlands.Global.Hecke.MixedSpaceUnfolding

/-!
# The product character on the mixed space

Properties of the product character
`χ(x) = ∏ (x_v / |x_v|)^{p_v} |x_v|^{t_v} ∏ (z_v / |z_v|)^{N_v} |z_v|^{2 u_v}`
(`mixedCharFun` of `Langlands.Global.Hecke.MixedSpaceFourier`) needed for the theta data of the
Hecke functional equation: multiplicativity and `χ(1) = 1`, the doubling relation
`χ(2 x) = χ(2) χ(x)` with `χ(2) ≠ 0`, measurability, the bound `|χ(x)| ≤ K N(x)^τ` on the
fundamental cone, and integrability of the zeta integrand `F_{p,N} χ N^(s-1)` of the product
Gaussian in its range of convergence.
-/

noncomputable section

open MeasureTheory NumberField NumberField.mixedEmbedding NumberField.InfinitePlace Module
open Complex
open scoped Real Classical ComplexConjugate

namespace Langlands.Global.Hecke

/-! ### The real and complex characters -/

section Characters

theorem realCharFun_mul (p : ℕ) (t : ℂ) (x y : ℝ) :
    realCharFun p t (x * y) = realCharFun p t x * realCharFun p t y := by
  simp only [realCharFun, abs_mul]
  rw [mul_div_mul_comm]
  push_cast
  rw [mul_pow, mul_cpow_ofReal_nonneg (abs_nonneg x) (abs_nonneg y)]
  ring

theorem realCharFun_one (p : ℕ) (t : ℂ) : realCharFun p t 1 = 1 := by
  simp [realCharFun]

theorem norm_realCharFun (p : ℕ) (t : ℂ) {x : ℝ} (hx : x ≠ 0) :
    ‖realCharFun p t x‖ = |x| ^ t.re := by
  rw [realCharFun, norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_div, abs_abs,
    div_self (abs_ne_zero.mpr hx), one_pow, one_mul,
    norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr hx)]

theorem complexCharFun_mul (N : ℤ) (u : ℂ) (z w : ℂ) :
    complexCharFun N u (z * w) = complexCharFun N u z * complexCharFun N u w := by
  simp only [complexCharFun, norm_mul]
  push_cast
  rw [mul_div_mul_comm, mul_zpow, mul_cpow_ofReal_nonneg (norm_nonneg z) (norm_nonneg w)]
  ring

theorem complexCharFun_one (N : ℤ) (u : ℂ) : complexCharFun N u 1 = 1 := by
  simp [complexCharFun]

theorem norm_complexCharFun (N : ℤ) (u : ℂ) {z : ℂ} (hz : z ≠ 0) :
    ‖complexCharFun N u z‖ = ‖z‖ ^ (2 * u.re) := by
  have hz' : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  rw [complexCharFun, norm_mul, norm_zpow, norm_div, norm_real, Real.norm_eq_abs,
    abs_of_pos hz', div_self hz'.ne', one_zpow, one_mul, norm_cpow_eq_rpow_re_of_pos hz']
  simp

theorem measurable_realCharFun (p : ℕ) (t : ℂ) : Measurable (realCharFun p t) := by
  unfold realCharFun
  fun_prop

theorem measurable_complexCharFun (N : ℤ) (u : ℂ) : Measurable (complexCharFun N u) := by
  unfold complexCharFun
  fun_prop

end Characters

/-! ### The product character -/

section Mixed

variable {K : Type*} [Field K] [NumberField K]
  (p : {w : InfinitePlace K // IsReal w} → Fin 2) (t : {w : InfinitePlace K // IsReal w} → ℂ)
  (N : {w : InfinitePlace K // IsComplex w} → ℤ) (u : {w : InfinitePlace K // IsComplex w} → ℂ)

theorem mixedCharFun_mul (x y : mixedSpace K) :
    mixedCharFun p t N u (x * y) = mixedCharFun p t N u x * mixedCharFun p t N u y := by
  simp only [mixedCharFun, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, realCharFun_mul,
    complexCharFun_mul, Finset.prod_mul_distrib]
  ring

theorem mixedCharFun_one : mixedCharFun p t N u (1 : mixedSpace K) = 1 := by
  simp [mixedCharFun, realCharFun_one, complexCharFun_one]

theorem measurable_mixedCharFun : Measurable (mixedCharFun p t N u) := by
  unfold mixedCharFun
  refine Measurable.mul (Finset.measurable_prod _ fun v _ => ?_)
    (Finset.measurable_prod _ fun v _ => ?_)
  · exact (measurable_realCharFun _ _).comp ((measurable_pi_apply v).comp measurable_fst)
  · exact (measurable_complexCharFun _ _).comp ((measurable_pi_apply v).comp measurable_snd)

theorem mixedCharFun_ne_zero {x : mixedSpace K} (h1 : ∀ v, x.1 v ≠ 0) (h2 : ∀ v, x.2 v ≠ 0) :
    mixedCharFun p t N u x ≠ 0 := by
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun v _ => ?_)
    (Finset.prod_ne_zero_iff.mpr fun v _ => ?_)
  · rw [← norm_ne_zero_iff, norm_realCharFun _ _ (h1 v)]
    exact (Real.rpow_pos_of_pos (abs_pos.mpr (h1 v)) _).ne'
  · rw [← norm_ne_zero_iff, norm_complexCharFun _ _ (h2 v)]
    exact (Real.rpow_pos_of_pos (norm_pos_iff.mpr (h2 v)) _).ne'

/-- The doubling constant `χ(2 • 1)` of the product character. -/
def mixedCharTwo : ℂ := mixedCharFun p t N u ((2 : ℝ) • (1 : mixedSpace K))

/-- Doubling multiplies the product character by the constant `χ(2 • 1)`. -/
theorem mixedCharFun_two_smul (x : mixedSpace K) :
    mixedCharFun p t N u ((2 : ℝ) • x) = mixedCharTwo p t N u * mixedCharFun p t N u x := by
  rw [mixedCharTwo, ← mixedCharFun_mul, smul_one_mul]

theorem mixedCharTwo_ne_zero : mixedCharTwo p t N u ≠ 0 := by
  refine mixedCharFun_ne_zero p t N u (fun v => ?_) (fun v => ?_)
  · simp
  · simp

/-- `y ^ a ≤ max (r ^ a) (R ^ a) * M ^ a` whenever `r M ≤ y ≤ R M` with `r, M > 0`. -/
theorem rpow_le_max_mul_rpow {r R M y : ℝ} (hr : 0 < r) (hM : 0 < M) (h1 : r * M ≤ y)
    (h2 : y ≤ R * M) (a : ℝ) : y ^ a ≤ max (r ^ a) (R ^ a) * M ^ a := by
  have hy : 0 < y := lt_of_lt_of_le (mul_pos hr hM) h1
  have hq1 : r ≤ y / M := by rw [le_div_iff₀ hM]; exact h1
  have hq2 : y / M ≤ R := by rw [div_le_iff₀ hM]; exact h2
  have hyM : y = y / M * M := by field_simp
  rw [hyM, Real.mul_rpow (div_pos hy hM).le hM.le]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hM.le a)
  rcases le_or_gt 0 a with ha | ha
  · exact (Real.rpow_le_rpow (div_pos hy hM).le hq2 ha).trans (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_nonpos hr hq1 ha.le).trans (le_max_left _ _)

/-- On the fundamental cone the product character is bounded by a power of the norm. -/
theorem exists_norm_mixedCharFun_le_cone :
    ∃ Kχ τ : ℝ, ∀ x ∈ fundamentalCone K,
      ‖mixedCharFun p t N u x‖ ≤ Kχ * mixedEmbedding.norm x ^ τ := by
  obtain ⟨r, R, hr, hR, hb⟩ := exists_normAtPlace_bounds (K := K)
  set n : ℝ := (finrank ℚ K : ℝ)⁻¹
  refine ⟨(∏ v, max (r ^ (t v).re) (R ^ (t v).re)) *
      ∏ v, max (r ^ (2 * (u v).re)) (R ^ (2 * (u v).re)),
    n * ((∑ v, (t v).re) + ∑ v, 2 * (u v).re), fun x hx => ?_⟩
  have hNpos := fundamentalCone.norm_pos_of_mem hx
  set M := mixedEmbedding.norm x ^ n with hM
  have hMpos : 0 < M := Real.rpow_pos_of_pos hNpos _
  have hreal : ∀ v : {w : InfinitePlace K // IsReal w}, r * M ≤ |x.1 v| ∧ |x.1 v| ≤ R * M :=
    fun v => by
      have h := hb x hx v.1
      rwa [normAtPlace_apply_of_isReal v.2, Real.norm_eq_abs] at h
  have hcx : ∀ v : {w : InfinitePlace K // IsComplex w}, r * M ≤ ‖x.2 v‖ ∧ ‖x.2 v‖ ≤ R * M :=
    fun v => by
      have h := hb x hx v.1
      rwa [normAtPlace_apply_of_isComplex v.2] at h
  have h1ne : ∀ v, x.1 v ≠ 0 := fun v =>
    abs_pos.mp (lt_of_lt_of_le (mul_pos hr hMpos) (hreal v).1)
  have h2ne : ∀ v, x.2 v ≠ 0 := fun v =>
    norm_pos_iff.mp (lt_of_lt_of_le (mul_pos hr hMpos) (hcx v).1)
  have hNτ : mixedEmbedding.norm x ^ (n * ((∑ v, (t v).re) + ∑ v, 2 * (u v).re)) =
      (∏ v, M ^ (t v).re) * ∏ v, M ^ (2 * (u v).re) := by
    rw [Real.rpow_mul hNpos.le, ← hM, Real.rpow_add hMpos, Real.rpow_sum_of_pos hMpos,
      Real.rpow_sum_of_pos hMpos]
  rw [mixedCharFun, norm_mul, norm_prod, norm_prod, hNτ]
  calc (∏ v, ‖realCharFun (p v) (t v) (x.1 v)‖) * ∏ v, ‖complexCharFun (N v) (u v) (x.2 v)‖
      ≤ (∏ v, max (r ^ (t v).re) (R ^ (t v).re) * M ^ (t v).re) *
          ∏ v, max (r ^ (2 * (u v).re)) (R ^ (2 * (u v).re)) * M ^ (2 * (u v).re) := by
        refine mul_le_mul (Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v _ => ?_)
          (Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v _ => ?_)
          (Finset.prod_nonneg fun v _ => norm_nonneg _)
          (Finset.prod_nonneg fun v _ => mul_nonneg
            (le_max_of_le_left (Real.rpow_nonneg hr.le _)) (Real.rpow_nonneg hMpos.le _))
        · rw [norm_realCharFun _ _ (h1ne v)]
          exact rpow_le_max_mul_rpow hr hMpos (hreal v).1 (hreal v).2 _
        · rw [norm_complexCharFun _ _ (h2ne v)]
          exact rpow_le_max_mul_rpow hr hMpos (hcx v).1 (hcx v).2 _
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
        ring

end Mixed

/-! ### Integrability of the zeta integrand -/

section Integrability

theorem integrable_norm_rpow_mul_exp_neg_mul_sq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {b : ℝ} (hb : 0 < b) {α : ℝ}
    (hα : -(finrank ℝ E : ℝ) < α) :
    Integrable (fun x : E => ‖x‖ ^ α * Real.exp (-b * ‖x‖ ^ 2)) μ := by
  refine (integrable_fun_norm_addHaar μ (f := fun y : ℝ => y ^ α * Real.exp (-b * y ^ 2))).2 ?_
  have hd : 1 ≤ finrank ℝ E := finrank_pos
  have h := integrableOn_rpow_mul_exp_neg_mul_sq hb (s := α + ((finrank ℝ E - 1 : ℕ) : ℝ)) (by
    rw [Nat.cast_sub hd, Nat.cast_one]
    linarith)
  refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
  simp only [smul_eq_mul]
  rw [Real.rpow_add hy, Real.rpow_natCast]
  ring

theorem ae_ne_zero_real : ∀ᵐ x : ℝ, x ≠ 0 := by
  simp [ae_iff, measure_singleton]

theorem ae_ne_zero_complex : ∀ᵐ z : ℂ, z ≠ 0 := by
  simp [ae_iff, measure_singleton]

theorem integrable_realGaussian_mul_realCharFun {b : ℝ} (hb : 0 < b) (p : ℕ) (t s : ℂ)
    (h : 0 < (s + t + p).re) :
    Integrable (fun x : ℝ => realGaussian b p x * realCharFun p t x *
      ((|x| : ℝ) : ℂ) ^ (s - 1)) := by
  have hα : -(finrank ℝ ℝ : ℝ) < (p : ℝ) + t.re + (s.re - 1) := by
    rw [finrank_self]
    simp only [add_re, natCast_re] at h
    push_cast
    linarith
  refine (integrable_norm_rpow_mul_exp_neg_mul_sq volume (mul_pos Real.pi_pos hb) hα).mono' ?_ ?_
  · exact (((continuous_realGaussian b p).measurable.mul (measurable_realCharFun p t)).mul
      (by fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_ne_zero_real] with x hx
    have hx' : 0 < |x| := abs_pos.mpr hx
    have hG : ‖realGaussian b p x‖ = |x| ^ p * Real.exp (-(π * b) * |x| ^ 2) := by
      rw [realGaussian, norm_mul, norm_pow, norm_real, Real.norm_eq_abs, Complex.norm_exp,
        sq_abs, show -((π : ℂ) * (b : ℂ) * (x : ℂ) ^ 2) = ((-(π * b) * x ^ 2 : ℝ) : ℂ) by
          push_cast; ring, ofReal_re]
    rw [norm_mul, norm_mul, hG, norm_realCharFun p t hx, norm_cpow_eq_rpow_re_of_pos hx',
      Real.norm_eq_abs, sub_re, one_re, Real.rpow_add hx', Real.rpow_add hx', Real.rpow_natCast]
    apply le_of_eq
    ring

theorem integrable_complexGaussian_mul_complexCharFun {b : ℝ} (hb : 0 < b) (N : ℤ) (u s : ℂ)
    (h : 0 < (s + u + N.natAbs / 2).re) :
    Integrable (fun z : ℂ => complexGaussian b N z * complexCharFun N u z *
      ((‖z‖ : ℝ) : ℂ) ^ (2 * (s - 1))) := by
  have hα : -(finrank ℝ ℂ : ℝ) < (N.natAbs : ℝ) + 2 * u.re + 2 * (s.re - 1) := by
    rw [Complex.finrank_real_complex]
    simp only [add_re, div_ofNat_re, natCast_re] at h
    push_cast
    linarith
  refine (integrable_norm_rpow_mul_exp_neg_mul_sq volume
    (by positivity : 0 < 2 * π * b) hα).mono' ?_ ?_
  · exact (((continuous_complexGaussian b N).measurable.mul (measurable_complexCharFun N u)).mul
      (by fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_ne_zero_complex] with z hz
    have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hN : N.toNat + (-N).toNat = N.natAbs := by omega
    have hG : ‖complexGaussian b N z‖ = ‖z‖ ^ N.natAbs * Real.exp (-(2 * π * b) * ‖z‖ ^ 2) := by
      rw [complexGaussian, norm_mul, norm_mul, norm_pow, norm_pow, RCLike.norm_conj,
        ← pow_add, hN, Complex.norm_exp,
        show -(2 * (π : ℂ) * (b : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2) =
          ((-(2 * π * b) * ‖z‖ ^ 2 : ℝ) : ℂ) by push_cast; ring, ofReal_re]
    rw [norm_mul, norm_mul, hG, norm_complexCharFun N u hz, norm_cpow_eq_rpow_re_of_pos hz',
      show (2 * (s - 1)).re = 2 * (s.re - 1) by simp, Real.rpow_add hz', Real.rpow_add hz',
      Real.rpow_natCast]
    apply le_of_eq
    ring

variable {K : Type*} [Field K] [NumberField K]

/-- The zeta integrand `F_{p,N} χ N^(s-1)` of the product Gaussian is integrable in the range of
convergence of `integral_mixedGaussian_mul_mixedCharFun`. -/
theorem integrable_mixedGaussian_mul_mixedCharFun
    (aR : {w : InfinitePlace K // IsReal w} → ℝ) (aC : {w : InfinitePlace K // IsComplex w} → ℂ)
    (p : {w : InfinitePlace K // IsReal w} → Fin 2) (t : {w : InfinitePlace K // IsReal w} → ℂ)
    (N : {w : InfinitePlace K // IsComplex w} → ℤ) (u : {w : InfinitePlace K // IsComplex w} → ℂ)
    (haR : ∀ v, aR v ≠ 0) (haC : ∀ v, aC v ≠ 0) (s : ℂ)
    (hR : ∀ v, 0 < (s + t v + (p v : ℕ)).re) (hC : ∀ v, 0 < (s + u v + (N v).natAbs / 2).re) :
    Integrable (fun x : mixedSpace K => mixedGaussian aR aC p N x * mixedCharFun p t N u x *
      ((mixedEmbedding.norm x : ℝ) : ℂ) ^ (s - 1)) := by
  have hint : ∀ x : mixedSpace K, mixedGaussian aR aC p N x * mixedCharFun p t N u x *
      ((mixedEmbedding.norm x : ℝ) : ℂ) ^ (s - 1) =
      (∏ v, realGaussian |aR v| (p v) (x.1 v) * realCharFun (p v) (t v) (x.1 v) *
        ((|x.1 v| : ℝ) : ℂ) ^ (s - 1)) *
      ∏ v, complexGaussian ‖aC v‖ (N v) (x.2 v) * complexCharFun (N v) (u v) (x.2 v) *
        ((‖x.2 v‖ : ℝ) : ℂ) ^ (2 * (s - 1)) := by
    intro x
    rw [norm_eq_prod_real_complex, ofReal_mul,
      mul_cpow_ofReal_nonneg (Finset.prod_nonneg fun v _ => abs_nonneg _)
        (Finset.prod_nonneg fun v _ => sq_nonneg _),
      Langlands.GodementJacquet.WhittakerTorus.ofReal_prod_cpow _ _ (fun v _ => abs_nonneg _),
      Langlands.GodementJacquet.WhittakerTorus.ofReal_prod_cpow _ _ (fun v _ => sq_nonneg _)]
    simp only [ofReal_sq_cpow (norm_nonneg _)]
    rw [mixedGaussian, mixedCharFun, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring
  have h1 := Integrable.fintype_prod (μ := fun _ => (volume : Measure ℝ))
    (f := fun v (x : ℝ) => realGaussian |aR v| (p v) x * realCharFun (p v) (t v) x *
      ((|x| : ℝ) : ℂ) ^ (s - 1))
    fun v => integrable_realGaussian_mul_realCharFun (abs_pos.mpr (haR v)) _ _ _ (hR v)
  have h2 := Integrable.fintype_prod (μ := fun _ => (volume : Measure ℂ))
    (f := fun v (z : ℂ) => complexGaussian ‖aC v‖ (N v) z * complexCharFun (N v) (u v) z *
      ((‖z‖ : ℝ) : ℂ) ^ (2 * (s - 1)))
    fun v => integrable_complexGaussian_mul_complexCharFun (norm_pos_iff.mpr (haC v)) _ _ _ (hC v)
  rw [← volume_pi] at h1 h2
  have hP := Integrable.mul_prod h1 h2
  rw [← Measure.volume_eq_prod] at hP
  exact hP.congr (ae_of_all _ fun x => (hint x).symm)

end Integrability

end Langlands.Global.Hecke
