import Langlands.LinearAlgebra.GMFamilySchwartzExtension
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Fourier integrals with the phase `e^{i⟪x, H⟫}`, coordinates and decay integrals

On a finite-dimensional real inner product space `V` with its Euclidean volume,
`phaseFourier u H = ∫ u(x) e^{i⟪x, H⟫} dx`. For a Schwartz function `u` it decays faster than
any power of `‖H‖`, with bounds by Schwartz seminorms of `u`, and its integral is
`(2π)^{dim V} u(0)`. Integration over `V` in the coordinates of a basis multiplies by the Gram
volume of the basis. Finally, for `c₀ > 0`, `A ≥ 0` and `s ≥ 0`, integrals over measurable sets
of coordinate vectors `X ∈ ℝ^ι` of functions bounded by
`A (1 + c₀ max(s, ‖X - y₀‖))^{-(n + |ι| + 1)}` are at most `C A (1 + s)^{-n}`, with `C` depending
only on `ι`, `n` and `c₀`. -/

noncomputable section

open scoped RealInnerProductSpace SchwartzMap FourierTransform
open MeasureTheory Complex

namespace Langlands.GMFamily

section PhaseFourier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Fourier integral `∫ u(x) e^{i⟪x, H⟫} dx`. -/
def phaseFourier (u : V → ℂ) (H : V) : ℂ :=
  ∫ x, u x * exp (I * (⟪x, H⟫ : ℂ))

theorem phaseFourier_eq_fourier (u : V → ℂ) (H : V) :
    phaseFourier u H = 𝓕 u (-(2 * Real.pi)⁻¹ • H) := by
  rw [phaseFourier, Real.fourier_eq']
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [smul_eq_mul, inner_smul_right]
  rw [mul_comm (u x)]
  congr 2
  push_cast
  field_simp

/-- **Decay of `phaseFourier` for Schwartz functions.** For every `N` there are `K` and `C ≥ 0`
such that `(1 + ‖H‖)^N |phaseFourier u H| ≤ C · schwartzSup K u` for every Schwartz function `u`
and every `H`. -/
theorem exists_phaseFourier_decay (N : ℕ) :
    ∃ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : 𝓢(V, ℂ)) (H : V),
      (1 + ‖H‖) ^ N * ‖phaseFourier u H‖ ≤ C * schwartzSup ℂ K u := by
  obtain ⟨K, C₁, hC₁, hb⟩ :=
    exists_schwartzSup_bound_schwartz (SchwartzMap.fourierTransformCLM ℂ (V := V) (E := ℂ)) N
  refine ⟨K, (2 * Real.pi) ^ N * 2 ^ N * C₁, by positivity, fun u H => ?_⟩
  set w : V := -(2 * Real.pi)⁻¹ • H with hw
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
  have hH : ‖H‖ = 2 * Real.pi * ‖w‖ := by
    rw [hw, norm_smul, norm_neg, norm_inv, Real.norm_of_nonneg (by positivity)]
    field_simp
  have h1 : (1 + ‖H‖) ^ N ≤ (2 * Real.pi) ^ N * (1 + ‖w‖) ^ N := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ N
    rw [hH]
    nlinarith [norm_nonneg w]
  have hf : phaseFourier (u : V → ℂ) H = SchwartzMap.fourierTransformCLM ℂ u w := by
    rw [phaseFourier_eq_fourier, SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe]
  have h2 : (1 + ‖w‖) ^ N * ‖SchwartzMap.fourierTransformCLM ℂ u w‖ ≤
      2 ^ N * schwartzSup ℂ N (SchwartzMap.fourierTransformCLM ℂ u) := by
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N, N))
      (le_refl N) (Nat.zero_le N) (SchwartzMap.fourierTransformCLM ℂ u) w
    rw [norm_iteratedFDeriv_zero] at h
    exact h
  calc (1 + ‖H‖) ^ N * ‖phaseFourier (u : V → ℂ) H‖
      ≤ (2 * Real.pi) ^ N * (1 + ‖w‖) ^ N * ‖SchwartzMap.fourierTransformCLM ℂ u w‖ := by
        rw [hf]; exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ ≤ (2 * Real.pi) ^ N * (2 ^ N * schwartzSup ℂ N (SchwartzMap.fourierTransformCLM ℂ u)) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ (2 * Real.pi) ^ N * (2 ^ N * (C₁ * schwartzSup ℂ K u)) := by
        gcongr; exact hb u
    _ = _ := by ring

/-- **Fourier inversion at the origin.** For a Schwartz function `u` on `V`,
`∫ phaseFourier u H dH = (2π)^{dim V} u(0)`. -/
theorem integral_phaseFourier (u : 𝓢(V, ℂ)) :
    ∫ H, phaseFourier u H = (2 * Real.pi) ^ Module.finrank ℝ V * u 0 := by
  simp_rw [phaseFourier_eq_fourier]
  rw [Measure.integral_comp_smul volume (fun w => 𝓕 (u : V → ℂ) w) (-(2 * Real.pi)⁻¹)]
  have hint : ∫ w, 𝓕 (u : V → ℂ) w = u 0 := by
    have hinv := Continuous.fourierInv_fourier_eq u.continuous u.integrable
      (by rw [← SchwartzMap.fourier_coe]; exact (𝓕 u).integrable)
    have h0 := congrFun hinv 0
    rw [Real.fourierInv_eq] at h0
    simpa using h0
  rw [hint, Complex.real_smul]
  congr 1
  rw [neg_pow, inv_pow, mul_inv, abs_mul, inv_inv, abs_inv, abs_pow, abs_neg, abs_one, one_pow,
    inv_one, one_mul, abs_of_pos (by positivity)]
  push_cast
  ring

end PhaseFourier

section Coordinates

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem volume_pi_eq_basisFun_addHaar (ι : Type*) [Fintype ι] :
    (Pi.basisFun ℝ ι).addHaar = (volume : Measure (ι → ℝ)) := by
  rw [Module.Basis.addHaar_eq_iff, Module.Basis.parallelepiped_basisFun]
  simp [TopologicalSpace.PositiveCompacts.piIcc01, Real.volume_Icc_pi]

/-- **Integration in the coordinates of a basis.** For a basis `b` of `V` and any `g : V → ℂ`,
`∫_V g = gram(b) · ∫_{ℝ^ι} g(∑_i X_i b_i) dX` (both sides vanish when `g` is not integrable). -/
theorem integral_eq_gramVolume_mul {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ V)
    (g : V → ℂ) :
    ∫ H, g H = (gramVolume (fun i => b i) : ℂ) * ∫ X : ι → ℝ, g (∑ i, X i • b i) := by
  classical
  let Φ : (ι → ℝ) ≃L[ℝ] V := b.equivFunL.symm
  have hΦ (X : ι → ℝ) : Φ X = ∑ i, X i • b i := by
    change b.equivFun.symm X = _
    rw [Module.Basis.equivFun_symm_apply]
  have hbasis : (Pi.basisFun ℝ ι).map Φ.toLinearEquiv = b := by
    ext i
    rw [Module.Basis.map_apply, Pi.basisFun_apply]
    change b.equivFun.symm (Pi.single i 1) = b i
    rw [Module.Basis.equivFun_symm_apply]
    simp [Pi.single_apply]
  have hmap : Measure.map Φ (volume : Measure (ι → ℝ)) = b.addHaar := by
    rw [← volume_pi_eq_basisFun_addHaar, Module.Basis.map_addHaar, hbasis]
  -- an orthonormal basis indexed by `ι`
  let o : OrthonormalBasis ι ℝ V := (stdOrthonormalBasis ℝ V).reindex
    (Fintype.equivOfCardEq (by simp [Module.finrank_eq_card_basis b]))
  have hgv : gramVolume (fun i => b i) = |o.toBasis.det b| := gramVolume_eq_abs_det o _
  have hpos : 0 < gramVolume (fun i => b i) := (gramVolume_pos_iff _).mpr b.linearIndependent
  have hpar : (volume : Measure V) (parallelepiped b) = ENNReal.ofReal (gramVolume fun i => b i) := by
    rw [← o.addHaar_eq_volume, Measure.addHaar_parallelepiped, hgv]
  have hvol : (volume : Measure V) = ENNReal.ofReal (gramVolume fun i => b i) • b.addHaar := by
    have h := Measure.addHaarMeasure_unique (volume : Measure V) b.parallelepiped
    rw [Module.Basis.coe_parallelepiped, hpar] at h
    rw [Module.Basis.addHaar_def]
    exact h
  have hemb : MeasurableEmbedding (Φ : (ι → ℝ) → V) := Φ.toHomeomorph.measurableEmbedding
  rw [hvol, integral_smul_measure, ENNReal.toReal_ofReal hpos.le, ← hmap,
    hemb.integral_map, Complex.real_smul]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun X => by
    change g (Φ X) = g (∑ i, X i • b i)
    rw [hΦ])

end Coordinates

section DecayIntegral

/-- For `c₀ > 0`, the weight `(1 + c₀‖X‖)^{-(|ι| + 1)}` is integrable on `ι → ℝ`. -/
theorem integrable_decay_weight (ι : Type*) [Fintype ι] {c₀ : ℝ} (hc₀ : 0 < c₀) :
    Integrable (fun X : ι → ℝ => ((1 + c₀ * ‖X‖) ^ (Fintype.card ι + 1))⁻¹) := by
  set N := Fintype.card ι + 1 with hN
  have hint := integrable_one_add_norm (E := ι → ℝ) (μ := volume) (r := N)
    (by simp [hN, Module.finrank_fintype_fun_eq_card])
  let m : ℝ := min 1 c₀
  have hm : 0 < m := lt_min one_pos hc₀
  refine (hint.const_mul ((m ^ N)⁻¹)).mono' ?_ (ae_of_all _ fun X => ?_)
  · exact (Continuous.inv₀ (f := fun X : ι → ℝ => (1 + c₀ * ‖X‖) ^ N) (by fun_prop)
      fun x => pow_ne_zero _ (by have := mul_nonneg hc₀.le (norm_nonneg x); linarith)).aestronglyMeasurable
  · have hX : 0 ≤ ‖X‖ := norm_nonneg X
    have h1 : m * (1 + ‖X‖) ≤ 1 + c₀ * ‖X‖ := by
      have := min_le_left 1 c₀
      have := min_le_right 1 c₀
      nlinarith
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg (by positivity), Real.rpow_natCast]
    rw [← mul_inv, ← mul_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h1 N)

/-- **Decay of coordinate integrals.** For `c₀ > 0` and `n` there is `C ≥ 0` such that for all
`A ≥ 0`, `s ≥ 0` and `y₀`, integrals over a measurable set `D` of coordinate vectors of functions
bounded on `D` by `A (1 + c₀ max(s, ‖X - y₀‖))^{-(n + |ι| + 1)}` are at most `C A (1 + s)^{-n}`. -/
theorem exists_integral_decay_bound (ι : Type*) [Fintype ι] (n : ℕ) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : (ι → ℝ) → ℂ) (D : Set (ι → ℝ)), MeasurableSet D →
      ∀ (A s : ℝ) (y₀ : ι → ℝ), 0 ≤ A → 0 ≤ s →
        (∀ X ∈ D, ‖F X‖ ≤ A * ((1 + c₀ * max s ‖X - y₀‖) ^ (n + Fintype.card ι + 1))⁻¹) →
        ‖∫ X in D, F X‖ ≤ C * A * ((1 + s) ^ n)⁻¹ := by
  set N := Fintype.card ι + 1 with hN
  let g : (ι → ℝ) → ℝ := fun X => ((1 + c₀ * ‖X‖) ^ N)⁻¹
  have hg_int : Integrable g := integrable_decay_weight ι hc₀
  let J := ∫ X, g X
  have hJ : 0 ≤ J := integral_nonneg fun X => by positivity
  let M := max 1 c₀⁻¹
  refine ⟨J * M ^ n, by positivity, fun F D hD A s y₀ hA hs hF => ?_⟩
  have hpt : ∀ X ∈ D, ‖F X‖ ≤ A * ((1 + c₀ * s) ^ n)⁻¹ * g (X - y₀) := by
    intro X hX
    refine (hF X hX).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hA
    have hb1 : 0 ≤ c₀ * s := by positivity
    have hb2 : 0 ≤ c₀ * ‖X - y₀‖ := by positivity
    have hm1 : 1 + c₀ * s ≤ 1 + c₀ * max s ‖X - y₀‖ := by
      nlinarith [le_max_left s ‖X - y₀‖]
    have hm2 : 1 + c₀ * ‖X - y₀‖ ≤ 1 + c₀ * max s ‖X - y₀‖ := by
      nlinarith [le_max_right s ‖X - y₀‖]
    have e1 : ((1 + c₀ * max s ‖X - y₀‖) ^ n)⁻¹ ≤ ((1 + c₀ * s) ^ n)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hm1 n)
    have e2 : ((1 + c₀ * max s ‖X - y₀‖) ^ N)⁻¹ ≤ ((1 + c₀ * ‖X - y₀‖) ^ N)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hm2 N)
    rw [show n + Fintype.card ι + 1 = n + N by omega, pow_add, mul_inv]
    exact mul_le_mul e1 e2 (by positivity) (by positivity)
  have hg' : Integrable (fun X => A * ((1 + c₀ * s) ^ n)⁻¹ * g (X - y₀)) :=
    (hg_int.comp_sub_right y₀).const_mul _
  have h1 : ‖∫ X in D, F X‖ ≤ ∫ X in D, A * ((1 + c₀ * s) ^ n)⁻¹ * g (X - y₀) :=
    norm_integral_le_of_norm_le hg'.integrableOn (ae_restrict_of_forall_mem hD hpt)
  have h2 : ∫ X in D, A * ((1 + c₀ * s) ^ n)⁻¹ * g (X - y₀) ≤
      ∫ X, A * ((1 + c₀ * s) ^ n)⁻¹ * g (X - y₀) :=
    setIntegral_le_integral hg' (ae_of_all _ fun X => by positivity)
  have h3 : ∫ X, A * ((1 + c₀ * s) ^ n)⁻¹ * g (X - y₀) = A * ((1 + c₀ * s) ^ n)⁻¹ * J := by
    rw [integral_const_mul, integral_sub_right_eq_self]
  have h4 : ((1 + c₀ * s) ^ n)⁻¹ ≤ M ^ n * ((1 + s) ^ n)⁻¹ := by
    have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_left _ _)
    have h5 : 1 + s ≤ M * (1 + c₀ * s) := by
      have hc : c₀⁻¹ * c₀ = 1 := inv_mul_cancel₀ hc₀.ne'
      have := le_max_left 1 c₀⁻¹
      have := le_max_right 1 c₀⁻¹
      nlinarith [mul_le_mul_of_nonneg_right (le_max_right 1 c₀⁻¹) (by positivity : 0 ≤ c₀ * s)]
    rw [← inv_pow, ← inv_pow, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ n
    rw [inv_le_comm₀ (by positivity) (by positivity), mul_inv, inv_inv]
    calc (1 + c₀ * s) = M * (1 + c₀ * s) * M⁻¹ := by field_simp
      _ ≥ (1 + s) * M⁻¹ := mul_le_mul_of_nonneg_right h5 (by positivity)
      _ = M⁻¹ * (1 + s) := mul_comm _ _
  calc ‖∫ X in D, F X‖ ≤ A * ((1 + c₀ * s) ^ n)⁻¹ * J := h1.trans (h2.trans h3.le)
    _ ≤ A * (M ^ n * ((1 + s) ^ n)⁻¹) * J := by gcongr
    _ = J * M ^ n * A * ((1 + s) ^ n)⁻¹ := by ring

end DecayIntegral

end Langlands.GMFamily
