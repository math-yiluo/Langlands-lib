import Langlands.Geometry.Manifold.SmoothGroupDifferential
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Integration by parts for invariant derivatives on a Lie group

For a real Lie group `G` modelled on a finite-dimensional space, a right-invariant measure
`μ` that is finite on compact sets, a smooth complex function `f` and a smooth compactly supported
`ψ`, the left-invariant derivative `X` satisfies `∫ (X f) ψ dμ = -∫ f (X ψ) dμ`. If moreover `μ`
is positive on nonempty open sets, a continuous function whose integrals against all smooth
compactly supported functions vanish is zero. -/

set_option autoImplicit false

noncomputable section

open scoped Classical Manifold ContDiff Topology
open MeasureTheory Set Filter

namespace Langlands.Geometry.Manifold

set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) ∞ G]

/-- The derivative of a smooth function along the right translates by an integral curve of the
left-invariant field of `X` is the invariant derivative at the translated point. -/
theorem hasDerivAt_mul_curve (X : GroupLieAlgebra 𝓘(ℝ, E) G) {f : G → ℂ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f) (x : G) {curve : ℝ → G} {t : ℝ}
    (hcurve : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) curve t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField X (curve t)))) :
    HasDerivAt (fun r => f (x * curve r))
      (groupDirectionalValue 𝓘(ℝ, E) X f (x * curve t)) t := by
  have horbit : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (fun h => f (x * h)) :=
    hf.comp (contMDiff_const.mul contMDiff_id)
  have hd := ((horbit.mdifferentiableAt (by simp)).hasMFDerivAt.comp t hcurve).hasFDerivAt.hasDerivAt
  have hd' : HasDerivAt (fun r => f (x * curve r))
      (mvfderiv 𝓘(ℝ, E) (fun h => f (x * h)) (curve t)
        (mulInvariantVectorField X (curve t))) t := by
    change HasDerivAt (fun r => f (x * curve r))
      (mvfderiv 𝓘(ℝ, E) (fun h => f (x * h)) (curve t)
        (((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField X (curve t))) 1)) t at hd
    simpa only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self,
      one_smul] using hd
  rw [← groupDirectionalValue_eq_invariant _ X horbit,
    groupDirectionalValue_leftTranslation] at hd'
  exact hd'

/-- The invariant derivative of a function vanishes off its topological support. -/
theorem groupDirectionalValue_eq_zero_of_notMem_tsupport (X : GroupLieAlgebra 𝓘(ℝ, E) G)
    {ψ : G → ℂ} {g : G} (hg : g ∉ tsupport ψ) :
    groupDirectionalValue 𝓘(ℝ, E) X ψ g = 0 := by
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ, E) ∞
  have hzero : (fun h => ψ (g * h)) =ᶠ[𝓝 (1 : G)] fun _ => (0 : ℂ) := by
    have hopen : IsOpen (tsupport ψ)ᶜ := (isClosed_tsupport ψ).isOpen_compl
    have hmem : (fun h : G => g * h) ⁻¹' (tsupport ψ)ᶜ ∈ 𝓝 (1 : G) := by
      apply (hopen.preimage (continuous_const.mul continuous_id)).mem_nhds
      simpa using hg
    filter_upwards [hmem] with h hh
    exact image_eq_zero_of_notMem_tsupport hh
  unfold groupDirectionalValue mvfderiv
  rw [hzero.mfderiv_eq, mfderiv_const]
  simp

/-- The topological support of an invariant derivative lies in that of the function. -/
theorem tsupport_groupDirectionalValue_subset (X : GroupLieAlgebra 𝓘(ℝ, E) G) (ψ : G → ℂ) :
    tsupport (groupDirectionalValue 𝓘(ℝ, E) X ψ) ⊆ tsupport ψ := by
  apply closure_minimal _ (isClosed_tsupport ψ)
  intro g hg
  by_contra hn
  exact hg (groupDirectionalValue_eq_zero_of_notMem_tsupport X hn)

/-- The invariant derivative of a compactly supported function is compactly supported. -/
theorem HasCompactSupport.groupDirectionalValue (X : GroupLieAlgebra 𝓘(ℝ, E) G) {ψ : G → ℂ}
    (hψ : HasCompactSupport ψ) :
    HasCompactSupport (groupDirectionalValue 𝓘(ℝ, E) X ψ) :=
  hψ.mono' ((subset_tsupport _).trans (tsupport_groupDirectionalValue_subset X ψ))

variable [CompleteSpace E]

/-- For every direction `X` there is a curve `c` with `c(0) = 1`, continuous on a closed ball,
along which every smooth `f` satisfies `d/dt f(x c(t)) = (X f)(x c(t))`. -/
theorem exists_groupDirectionalCurve (X : GroupLieAlgebra 𝓘(ℝ, E) G) :
    ∃ (curve : ℝ → G) (ε : ℝ), 0 < ε ∧ curve 0 = 1 ∧
      ContinuousOn curve (Metric.closedBall 0 ε) ∧
      ∀ (f : G → ℂ), ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f → ∀ (x : G),
        ∀ t ∈ Metric.ball (0 : ℝ) ε,
          HasDerivAt (fun r => f (x * curve r))
            (groupDirectionalValue 𝓘(ℝ, E) X f (x * curve t)) t := by
  let model := 𝓘(ℝ, E)
  let : LieGroup model (minSmoothness ℝ 3) G := LieGroup.of_le (n := ∞) (by simp)
  let v : (x : G) → TangentSpace model x := mulInvariantVectorField X
  have hv : ContMDiff model model.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle model G)) :=
    (contMDiff_mulInvariantVectorField X).of_le (by simp)
  obtain ⟨curve, hcurve_zero, hintegral_curve⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless 0 (x₀ := (1 : G)) hv.contMDiffAt
  obtain ⟨ε, hε, hcurve⟩ := Metric.eventually_nhds_iff_ball.mp hintegral_curve
  refine ⟨curve, ε / 2, half_pos hε, hcurve_zero, fun t ht => ?_, fun f hf x t ht => ?_⟩
  · exact (hcurve _ (Metric.closedBall_subset_ball (half_lt_self hε) ht)).continuousAt
      |>.continuousWithinAt
  · exact hasDerivAt_mul_curve X hf x
      (hcurve t (Metric.ball_subset_ball (half_le_self hε.le) ht))

variable [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- Integration by parts for an invariant derivative against a right-invariant measure. -/
theorem integral_groupDirectionalValue_mul (μ : Measure G) [μ.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μ] (X : GroupLieAlgebra 𝓘(ℝ, E) G) {f ψ : G → ℂ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f) (hψ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ x, groupDirectionalValue 𝓘(ℝ, E) X f x * ψ x ∂μ =
      -∫ x, f x * groupDirectionalValue 𝓘(ℝ, E) X ψ x ∂μ := by
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ, E) ∞
  obtain ⟨curve, ε, hε, hc0, hcc, hderiv⟩ := exists_groupDirectionalCurve (G := G) X
  set Df := groupDirectionalValue 𝓘(ℝ, E) X f with hDf
  set Dψ := groupDirectionalValue 𝓘(ℝ, E) X ψ with hDψ
  have hDfc : Continuous Df := (contMDiff_groupDirectionalValue _ X hf).continuous
  have hDψc : Continuous Dψ := (contMDiff_groupDirectionalValue _ X hψ).continuous
  have hfc : Continuous f := hf.continuous
  have hψcont : Continuous ψ := hψ.continuous
  let D : G → ℂ := fun y => Df y * ψ y + f y * Dψ y
  have hDc : Continuous D := (hDfc.mul hψcont).add (hfc.mul hDψc)
  have hDzero : ∀ y, y ∉ tsupport ψ → D y = 0 := by
    intro y hy
    have h1 : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
    have h2 : Dψ y = 0 := groupDirectionalValue_eq_zero_of_notMem_tsupport X hy
    simp [D, h1, h2]
  set B := curve '' Metric.closedBall (0 : ℝ) ε with hB
  have hBc : IsCompact B := (isCompact_closedBall 0 ε).image_of_continuousOn hcc
  set K := (fun p : G × G => p.1 * p.2⁻¹) '' (tsupport ψ ×ˢ B) with hK
  have hKc : IsCompact K :=
    (hψc.isCompact.prod hBc).image (continuous_fst.mul continuous_snd.inv)
  obtain ⟨C₀, hC₀⟩ :=
    (hψc.isCompact.image_of_continuousOn hDc.continuousOn).isBounded.exists_norm_le
  set C := max C₀ 0 with hCdef
  have hbound : ∀ x, ∀ t ∈ Metric.ball (0 : ℝ) ε,
      ‖D (x * curve t)‖ ≤ K.indicator (fun _ => C) x := by
    intro x t ht
    by_cases hx : x * curve t ∈ tsupport ψ
    · have hxK : x ∈ K :=
        ⟨(x * curve t, curve t), ⟨hx, t, Metric.ball_subset_closedBall ht, rfl⟩, by simp⟩
      rw [indicator_of_mem hxK]
      exact (hC₀ _ ⟨_, hx, rfl⟩).trans (le_max_left _ _)
    · rw [hDzero _ hx, norm_zero]
      exact indicator_nonneg (fun _ _ => le_max_right _ _) x
  let Φ : ℝ → G → ℂ := fun t x => f (x * curve t) * ψ (x * curve t)
  let Φ' : ℝ → G → ℂ := fun t x => D (x * curve t)
  have hΦd : ∀ x, ∀ t ∈ Metric.ball (0 : ℝ) ε, HasDerivAt (fun r => Φ r x) (Φ' t x) t := by
    intro x t ht
    exact (hderiv f hf x t ht).mul (hderiv ψ hψ x t ht)
  have hΦcont (t : ℝ) : Continuous (Φ t) :=
    (hfc.comp (continuous_id.mul continuous_const)).mul
      (hψcont.comp (continuous_id.mul continuous_const))
  have hfψ : HasCompactSupport (fun x => f x * ψ x) := hψc.mul_left
  have hΦ0 : Φ 0 = fun x => f x * ψ x := by
    funext x
    simp [Φ, hc0]
  have hΦ'0 : Φ' 0 = D := by
    funext x
    simp [Φ', hc0]
  have hint0 : Integrable (Φ 0) μ := by
    rw [hΦ0]
    exact (hfc.mul hψcont).integrable_of_hasCompactSupport hfψ
  have hbint : Integrable (K.indicator (fun _ => C)) μ :=
    (integrableOn_const (C := C) hKc.measure_lt_top.ne).integrable_indicator hKc.measurableSet
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (F := Φ) (F' := Φ') (bound := K.indicator (fun _ => C))
    (Metric.ball_mem_nhds 0 hε)
    (Eventually.of_forall fun t => (hΦcont t).aestronglyMeasurable) hint0
    (by rw [hΦ'0]; exact hDc.aestronglyMeasurable)
    (ae_of_all _ fun x t ht => hbound x t ht) hbint
    (ae_of_all _ fun x t ht => hΦd x t ht)
  have hconst : (fun t => ∫ x, Φ t x ∂μ) = fun _ => ∫ x, f x * ψ x ∂μ := by
    funext t
    exact integral_mul_right_eq_self (μ := μ) (fun x => f x * ψ x) (curve t)
  have hzero : ∫ x, Φ' 0 x ∂μ = 0 := by
    have h := hmain.2
    rw [hconst] at h
    exact h.unique (hasDerivAt_const 0 _)
  rw [hΦ'0] at hzero
  have hint1 : Integrable (fun x => Df x * ψ x) μ :=
    (hDfc.mul hψcont).integrable_of_hasCompactSupport hψc.mul_left
  have hint2 : Integrable (fun x => f x * Dψ x) μ :=
    (hfc.mul hDψc).integrable_of_hasCompactSupport
      (HasCompactSupport.groupDirectionalValue X hψc).mul_left
  have hsplit : ∫ x, D x ∂μ = ∫ x, Df x * ψ x ∂μ + ∫ x, f x * Dψ x ∂μ :=
    integral_add hint1 hint2
  rw [hsplit] at hzero
  exact eq_neg_of_add_eq_zero_left hzero

omit [CompleteSpace E] in
/-- A continuous function whose integrals against all smooth compactly supported functions
vanish is zero, for a measure that is positive on nonempty open sets. -/
theorem eq_zero_of_forall_integral_mul_eq_zero [FiniteDimensional ℝ E] (μ : Measure G)
    [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ] {Θ : G → ℂ} (hΘ : Continuous Θ)
    (h : ∀ ψ : G → ℂ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ ψ → HasCompactSupport ψ →
      ∫ x, Θ x * ψ x ∂μ = 0) :
    Θ = 0 := by
  funext x₀
  by_contra hne
  set a := (starRingEnd ℂ) (Θ x₀) with ha
  let R : G → ℝ := fun x => (a * Θ x).re
  have hR : Continuous R := Complex.continuous_re.comp (continuous_const.mul hΘ)
  have hR0 : 0 < R x₀ := by
    have : a * Θ x₀ = (Complex.normSq (Θ x₀) : ℂ) := by
      rw [ha, Complex.normSq_eq_conj_mul_self]
    simp only [R, this, Complex.ofReal_re]
    exact Complex.normSq_pos.mpr hne
  have hU : {x | 0 < R x} ∈ 𝓝 x₀ := (isOpen_lt continuous_const hR).mem_nhds hR0
  obtain ⟨b, -, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) x₀).mem_iff.mp hU
  let β : G → ℝ := fun x => b x
  have hβs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ β := b.contMDiff
  have hβc : HasCompactSupport β := b.hasCompactSupport
  let L : ℝ →L[ℝ] ℂ := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) a
  let ψ : G → ℂ := fun x => L (β x)
  have hψs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ ψ := L.contDiff.contMDiff.comp hβs
  have hψc : HasCompactSupport ψ := hβc.comp_left (map_zero L)
  have hint := h ψ hψs hψc
  let g : G → ℝ := fun x => R x * β x
  have hgc : Continuous g := hR.mul hβs.continuous
  have hgcs : HasCompactSupport g := hβc.mul_left
  have hgnn : 0 ≤ g := by
    intro x
    by_cases hx : x ∈ tsupport β
    · exact mul_nonneg (hb hx).le (b.nonneg)
    · simp [g, image_eq_zero_of_notMem_tsupport hx]
  have hg0 : g x₀ ≠ 0 := by
    simp only [g, β, b.eq_one, mul_one]
    exact hR0.ne'
  have hpos : 0 < ∫ x, g x ∂μ := hgc.integral_pos_of_hasCompactSupport_nonneg_nonzero hgcs hgnn hg0
  have hre : ∫ x, g x ∂μ = (∫ x, Θ x * ψ x ∂μ).re := by
    have hI : Integrable (fun x => Θ x * ψ x) μ :=
      (hΘ.mul hψs.continuous).integrable_of_hasCompactSupport hψc.mul_left
    have hre' := integral_re hI
    simp only [RCLike.re_to_complex] at hre'
    rw [← hre']
    congr 1
    funext x
    simp only [g, R, ψ, L, ContinuousLinearMap.smulRight_apply, one_apply_eq_self]
    rw [show Θ x * ((β x) • a) = (a * Θ x) * (β x : ℂ) by rw [Complex.real_smul]; ring,
      Complex.re_mul_ofReal]
  rw [hre, hint, Complex.zero_re] at hpos
  exact lt_irrefl _ hpos

end Langlands.Geometry.Manifold
