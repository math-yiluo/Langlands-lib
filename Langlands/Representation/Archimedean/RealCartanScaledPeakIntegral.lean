import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Rescaled peak integrals with compact parameters -/

noncomputable section

open Filter Set MeasureTheory Metric Module
open scoped Topology Pointwise

namespace Langlands.Archimedean.RealCartanScaledPeakIntegral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {F : Type*} [NormedAddCommGroup F]

/-- The cone bump of height one with support in the open unit ball. -/
def cone (y : F) : ℝ := max 0 (1 - ‖y‖)

theorem continuous_cone : Continuous (cone : F → ℝ) :=
  continuous_const.max (continuous_const.sub continuous_norm)

theorem cone_nonneg (y : F) : 0 ≤ cone y := le_max_left _ _

theorem cone_le_one (y : F) : cone y ≤ 1 :=
  max_le zero_le_one (sub_le_self _ (norm_nonneg y))

theorem cone_eq_zero_of_one_le {y : F} (hy : 1 ≤ ‖y‖) : cone y = 0 :=
  max_eq_left (sub_nonpos.mpr hy)

variable {P E : Type*} [TopologicalSpace P] [CompactSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F]

omit [TopologicalSpace P] [CompactSpace P] [FiniteDimensional ℝ E] in
private theorem linear_bound_of_unit_sphere (D : P → E →L[ℝ] F) (m : ℝ)
    (h : ∀ p (z : E), ‖z‖ = 1 → m ≤ ‖D p z‖) (p : P) (z : E) :
    m * ‖z‖ ≤ ‖D p z‖ := by
  by_cases hz : z = 0
  · simp [hz]
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have he : ‖‖z‖⁻¹ • z‖ = 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ hn.ne']
    have hnorm := h p (‖z‖⁻¹ • z) he
    rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_eq_div] at hnorm
    exact (le_div_iff₀ hn).mp hnorm

/-- A continuous compact family of injective differentials has a uniform lower bound. -/
theorem exists_linear_bound (D : P → E →L[ℝ] F) (hD : Continuous D)
    (hinj : ∀ p, Function.Injective (D p)) :
    ∃ m > 0, ∀ p z, m * ‖z‖ ≤ ‖D p z‖ := by
  let S := (univ : Set P) ×ˢ sphere (0 : E) 1
  have hS : IsCompact S := isCompact_univ.prod (isCompact_sphere _ _)
  by_cases hne : S.Nonempty
  · let N (p : P × E) := ‖D p.1 p.2‖
    have hN : Continuous N := ((hD.comp continuous_fst).clm_apply continuous_snd).norm
    obtain ⟨p, hp, hm⟩ := hS.exists_isMinOn hne hN.continuousOn
    have hp1 : ‖p.2‖ = 1 := mem_sphere_zero_iff_norm.mp hp.2
    have hz : p.2 ≠ 0 := by intro hz; simp [hz] at hp1
    have hDp : D p.1 p.2 ≠ 0 := fun he => hz ((hinj p.1) (he.trans (map_zero _).symm))
    have hpos : 0 < N p := norm_pos_iff.mpr hDp
    exact ⟨N p, hpos, linear_bound_of_unit_sphere D _ fun q z hz =>
      (isMinOn_iff.mp hm) (q, z) ⟨mem_univ _, mem_sphere_zero_iff_norm.mpr hz⟩⟩
  · refine ⟨1, zero_lt_one, linear_bound_of_unit_sphere D _ ?_⟩
    intro p z hz
    exact (hne ⟨(p, z), mem_univ _, mem_sphere_zero_iff_norm.mpr hz⟩).elim

/-- Continuous transverse derivatives that are injective at zero give a
uniform linear lower bound in a sufficiently small source ball. -/
theorem exists_nonlinear_bound (f : P → E → F) (A : P × E → E →L[ℝ] F)
    (hA : Continuous A) (hderiv : ∀ p z, HasFDerivAt (f p) (A (p, z)) z)
    (hf₀ : ∀ p, f p 0 = 0) (hinj : ∀ p, Function.Injective (A (p, 0))) :
    ∃ r > 0, ∃ m > 0, ∀ p z, ‖z‖ ≤ r → m * ‖z‖ ≤ ‖f p z‖ := by
  let D (p : P) := A (p, 0)
  have hD : Continuous D := hA.comp (continuous_id.prodMk continuous_const)
  obtain ⟨m, hm, hlinear⟩ := exists_linear_bound D hD hinj
  let U := {p : P × E | ‖A p - D p.1‖ < m / 2}
  have hU : IsOpen U := isOpen_lt (hA.sub (hD.comp continuous_fst)).norm continuous_const
  have h0 : (univ : Set P) ×ˢ {(0 : E)} ⊆ U := by
    rintro ⟨p, z⟩ ⟨_, hz⟩
    have hz' : z = 0 := hz
    subst z
    change ‖A (p, 0) - A (p, 0)‖ < m / 2
    rw [sub_self, norm_zero]
    positivity
  obtain ⟨B, V, _, hV, hB, hzV, hBV⟩ := generalized_tube_lemma isCompact_univ
    isCompact_singleton hU h0
  obtain ⟨r, hr, hrV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hV.mem_nhds (hzV (mem_singleton 0)))
  refine ⟨r, hr, m / 2, by positivity, fun p z hz => ?_⟩
  have h₀ : (0 : E) ∈ closedBall (0 : E) r := mem_closedBall_self hr.le
  have hz' : z ∈ closedBall (0 : E) r := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hderiv' (u : E) (hu : u ∈ closedBall (0 : E) r) :
      HasFDerivWithinAt (fun y => f p y - D p y) (A (p, u) - D p) (closedBall 0 r) u :=
    ((hderiv p u).sub (D p).hasFDerivAt).hasFDerivWithinAt
  have hA' (u : E) (hu : u ∈ closedBall (0 : E) r) : ‖A (p, u) - D p‖ ≤ m / 2 :=
    (show (p, u) ∈ U from hBV ⟨hB (mem_univ p), hrV hu⟩).le
  have herror := (convex_closedBall (0 : E) r).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hderiv' hA' h₀ hz'
  simp only [hf₀, map_zero, sub_zero] at herror
  have htri : ‖D p z‖ ≤ ‖f p z‖ + ‖f p z - D p z‖ := by
    calc
      ‖D p z‖ = ‖f p z - (f p z - D p z)‖ := by rw [sub_sub_cancel]
      _ ≤ _ := norm_sub_le _ _
  linarith [hlinear p z]

omit [CompactSpace P] [FiniteDimensional ℝ E] in
private theorem continuous_rescaledIntegrand {f : P → E → F} {w : P → E → ℂ}
    (hf : Continuous (Function.uncurry f)) (hw : Continuous (Function.uncurry w)) (ε : ℝ) :
    Continuous fun p : P × E =>
      (cone (ε⁻¹ • f p.1 (ε • p.2)) : ℂ) * w p.1 (ε • p.2) := by
  have h : Continuous fun p : P × E => (p.1, ε • p.2) :=
    continuous_fst.prodMk (continuous_const.smul continuous_snd)
  exact (Complex.continuous_ofReal.comp (continuous_cone.comp
    (continuous_const.smul (hf.comp h)))).mul (hw.comp h)

omit [CompactSpace P] [FiniteDimensional ℝ E] in
private theorem continuous_limitIntegrand {D : P → E →L[ℝ] F} {w : P → E → ℂ}
    (hD : Continuous D) (hw : Continuous (Function.uncurry w)) :
    Continuous fun p : P × E => (cone (D p.1 p.2) : ℂ) * w p.1 0 :=
  (Complex.continuous_ofReal.comp (continuous_cone.comp
    ((hD.comp continuous_fst).clm_apply continuous_snd))).mul
      (hw.comp (continuous_fst.prodMk continuous_const))

section Measure

variable [T2Space P] [MeasurableSpace P] [BorelSpace P] [SecondCountableTopology P]
  [MeasurableSpace E] [BorelSpace E]

/-- Rescale the source coordinates by the peak radius. The integral on a
small source ball tends to the integral of the bump of the linearization,
with the weight evaluated at the center. -/
def RealCartanScaledPeakIntegralStatement (P E F : Type*) [TopologicalSpace P]
    [CompactSpace P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [SecondCountableTopology P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] : Prop :=
  ∀ (μ : Measure P) [IsFiniteMeasure μ] (ν : Measure E) [ν.IsAddHaarMeasure]
    (f : P → E → F) (D : P → E →L[ℝ] F) (w : P → E → ℂ) (r m : ℝ),
    Continuous (Function.uncurry f) → Continuous D → Continuous (Function.uncurry w) →
    (∀ p, f p 0 = 0) → (∀ p, HasFDerivAt (f p) (D p) 0) →
    0 < r → 0 < m →
    (∀ p z, ‖z‖ ≤ r → m * ‖z‖ ≤ ‖f p z‖) →
    (∀ p z, m * ‖z‖ ≤ ‖D p z‖) →
    Tendsto (fun ε : ℝ => (ε ^ finrank ℝ E)⁻¹ •
      (∫ p, ∫ z in closedBall (0 : E) r, (cone (ε⁻¹ • f p z) : ℂ) * w p z ∂ν ∂μ))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ p, ∫ z, (cone (D p z) : ℂ) * w p 0 ∂ν ∂μ))

set_option maxHeartbeats 1000000 in
theorem realCartanScaledPeakIntegral : RealCartanScaledPeakIntegralStatement P E F := by
  intro μ _ ν _ f D w r m hf hD hw hf₀ hd hr hm hbound hlinear
  let R := m⁻¹
  let S := closedBall (0 : E) R
  let η := μ.prod (ν.restrict S)
  let L : Filter ℝ := 𝓝[>] (0 : ℝ)
  let I (ε : ℝ) (p : P × E) := (cone (ε⁻¹ • f p.1 (ε • p.2)) : ℂ) * w p.1 (ε • p.2)
  let I₀ (p : P × E) := (cone (D p.1 p.2) : ℂ) * w p.1 0
  have hI (ε : ℝ) : Continuous (I ε) := continuous_rescaledIntegrand hf hw ε
  have hI₀ : Continuous I₀ := continuous_limitIntegrand hD hw
  have hS : IsCompact S := isCompact_closedBall _ _
  have hprod : (μ.prod ν).restrict (univ ×ˢ S) = η := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hIntegrable (g : P × E → ℂ) (hg : Continuous g) : Integrable g η := by
    rw [← hprod]
    exact hg.continuousOn.integrableOn_compact (isCompact_univ.prod hS)
  have hSae : ∀ᵐ q : P × E ∂η, q.2 ∈ S := by
    rw [← hprod, ae_restrict_iff' (MeasurableSet.univ.prod hS.isClosed.measurableSet)]
    exact ae_of_all _ fun _ hq => hq.2
  obtain ⟨C, hC⟩ := (isCompact_univ.prod (isCompact_closedBall (0 : E) r)).exists_bound_of_continuousOn
    hw.continuousOn
  have hsmall : ∀ᶠ ε : ℝ in L, 0 < ε ∧ ε * R < r := by
    have hv : Tendsto (fun ε : ℝ => ε * R) L (𝓝 (0 : ℝ)) := by
      have hc : Continuous (fun ε : ℝ => ε * R) := continuous_id.mul continuous_const
      simpa only [zero_mul] using hc.continuousAt.tendsto.mono_left
        (show L ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    have hpos : ∀ᶠ ε : ℝ in L, ε ∈ Ioi 0 := self_mem_nhdsWithin
    exact hpos.and (hv.eventually (gt_mem_nhds hr))
  have hscale (ε : ℝ) (hε : 0 < ε) (he : ε * R < r) {z : E} (hz : z ∈ S) :
      ε • z ∈ closedBall (0 : E) r := by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hε.le]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz) hε.le).trans he.le
  have hlim (p : P × E) : Tendsto (fun ε => I ε p) L (𝓝 (I₀ p)) := by
    have ht : Tendsto (fun ε : ℝ => ε⁻¹ • f p.1 (ε • p.2)) L (𝓝 (D p.1 p.2)) := by
      have hline := ((hd p.1).hasLineDerivAt (v := p.2)).tendsto_slope_zero_right
      simpa only [slope_def_module, zero_add, sub_zero, hf₀] using hline
    have hz : Tendsto (fun ε : ℝ => ε • p.2) L (𝓝 (0 : E)) := by
      have hc : Continuous (fun ε : ℝ => ε • p.2) := continuous_id.smul continuous_const
      simpa only [zero_smul] using hc.continuousAt.tendsto.mono_left
        (show L ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    exact ((Complex.continuous_ofReal.comp continuous_cone).continuousAt.tendsto.comp ht).mul
      (hw.continuousAt.tendsto.comp (tendsto_const_nhds.prodMk_nhds hz))
  have hconst : Integrable (fun _ : P × E => max C 0) η := by
    rw [← hprod]
    exact continuous_const.continuousOn.integrableOn_compact (isCompact_univ.prod hS)
  have hlimit : Tendsto (fun ε => ∫ q, I ε q ∂η) L (𝓝 (∫ q, I₀ q ∂η)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => max C 0)
      (Eventually.of_forall fun ε => (hIntegrable _ (hI ε)).aestronglyMeasurable) _ hconst
      (ae_of_all _ hlim)
    filter_upwards [hsmall] with ε he
    filter_upwards [hSae] with q hq
    have hC' := hC (q.1, ε • q.2) ⟨mem_univ _, hscale ε he.1 he.2 hq⟩
    change ‖w q.1 (ε • q.2)‖ ≤ C at hC'
    change ‖(cone (ε⁻¹ • f q.1 (ε • q.2)) : ℂ) * w q.1 (ε • q.2)‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (cone_nonneg _)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (cone_le_one _)).trans (hC'.trans (le_max_left _ _))
  have hlimit_eq : (∫ q, I₀ q ∂η) = ∫ p, ∫ z, (cone (D p z) : ℂ) * w p 0 ∂ν ∂μ := by
    rw [integral_prod _ (hIntegrable _ hI₀)]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      have h := hlinear p z
      have hRz : R < ‖z‖ := lt_of_not_ge fun h => hz (mem_closedBall_zero_iff.mpr h)
      have hb : 1 ≤ ‖D p z‖ := by
        have hc := mul_le_mul_of_nonneg_left hRz.le hm.le
        rw [show m * R = 1 from mul_inv_cancel₀ hm.ne'] at hc
        exact hc.trans h
      simp [I₀, cone_eq_zero_of_one_le hb]
  rw [hlimit_eq] at hlimit
  refine hlimit.congr' ?_
  filter_upwards [hsmall] with ε he
  have hs : ε • S ⊆ closedBall (0 : E) r := by
    rintro z ⟨y, hy, rfl⟩
    exact hscale ε he.1 he.2 hy
  rw [integral_prod _ (hIntegrable _ (hI ε)), ← integral_smul]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  let g (z : E) := (cone (ε⁻¹ • f p z) : ℂ) * w p z
  change (∫ z in S, g (ε • z) ∂ν) = (ε ^ finrank ℝ E)⁻¹ •
    (∫ z in closedBall (0 : E) r, g z ∂ν)
  rw [Measure.setIntegral_comp_smul_of_pos ν g S he.1]
  congr 1
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_closedBall hs
  intro z hz
  have hz' : R < ‖ε⁻¹ • z‖ := lt_of_not_ge fun hn => hz.2
    ((mem_smul_set_iff_inv_smul_mem₀ he.1.ne' S z).mpr (mem_closedBall_zero_iff.mpr hn))
  have hx := hbound p z (mem_closedBall_zero_iff.mp hz.1)
  have hnorm (v : E) : ‖ε⁻¹ • v‖ = ε⁻¹ * ‖v‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr he.1.le)]
  have hb : 1 ≤ ‖ε⁻¹ • f p z‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr he.1.le)]
    calc
      1 = m * R := (mul_inv_cancel₀ hm.ne').symm
      _ ≤ m * ‖ε⁻¹ • z‖ := mul_le_mul_of_nonneg_left hz'.le hm.le
      _ = ε⁻¹ * (m * ‖z‖) := by rw [hnorm]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr he.1.le)
  simp [g, cone_eq_zero_of_one_le hb]

end Measure

end Langlands.Archimedean.RealCartanScaledPeakIntegral
