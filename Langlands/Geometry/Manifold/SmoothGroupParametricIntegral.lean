import Langlands.Geometry.Manifold.SmoothGroupUniformLimit
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # Differentiation under the integral sign with invariant derivatives

Let `G` be a Lie group modelled on a finite-dimensional real space and `μ` a measure on a
measurable space `Ω`. Let `f a x : G → ℂ` be smooth functions indexed by `a : A` and `x : Ω`,
closed under invariant differentiation through an index transition `step`, and dominated locally
uniformly in `g` by integrable functions of `x`. Then every `g ↦ ∫ f a x g dμ` is smooth and its
invariant derivatives are the integrals of the invariant derivatives. -/

noncomputable section

open Filter Set MeasureTheory
open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [LieGroup 𝓘(ℝ, E) ∞ G]
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {A : Type*}

local notation "𝓘E" => 𝓘(ℝ, E)
local notation "J" => Fin (Module.finrank ℝ E)

variable {f : A → Ω → G → ℂ}

omit [FiniteDimensional ℝ E] in
/-- In the extended chart at the identity, the derivative of a left translate in direction `X`
is the invariant derivative. -/
private theorem fderiv_chart_leftTranslate (u : G → ℂ) (hu : ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ u)
    (x₀ : G) (X : E) :
    fderiv ℝ ((fun y => u (x₀ * y)) ∘ (extChartAt 𝓘E (1 : G)).symm)
        (extChartAt 𝓘E (1 : G) 1) X = groupDirectionalValue 𝓘E X u x₀ := by
  let e := extChartAt 𝓘E (1 : G)
  have hS : IsOpen e.target := isOpen_extChartAt_target (I := 𝓘E) (1 : G)
  have he : e 1 ∈ e.target := e.map_source (mem_extChartAt_source (1 : G))
  have he₁ : e.symm (e 1) = 1 := e.left_inv (mem_extChartAt_source (1 : G))
  let v (y : G) := u (x₀ * y)
  have hv : ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ v := hu.comp (contMDiff_const.mul contMDiff_id)
  have hMD : MDifferentiableAt 𝓘E 𝓘E (e.symm : E → G) (e 1) :=
    ((contMDiffOn_extChartAt_symm (I := 𝓘E) (n := ∞) (1 : G) (e 1) he).contMDiffAt
      (hS.mem_nhds he)).mdifferentiableAt (by simp)
  change fderiv ℝ (v ∘ e.symm) (e 1) X = mvfderiv 𝓘E v 1 X
  have hc := mvfderiv_comp_apply_of_eq (I := 𝓘E) (I' := 𝓘E) (e 1)
    (hv.mdifferentiableAt (by simp)) hMD he₁ (X : TangentSpace 𝓘E (e 1))
  have hide := mfderivWithin_range_extChartAt_symm (I := 𝓘E) (x := (1 : G))
  rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hide
  have hide' : mfderiv 𝓘E 𝓘E (e.symm : E → G) (e 1) =
      ContinuousLinearMap.id ℝ (TangentSpace 𝓘E (e 1)) := hide
  rw [hide'] at hc
  change mvfderiv 𝓘E (v ∘ e.symm) (e 1) X = mvfderiv 𝓘E v 1 X at hc
  rw [mvfderiv_eq_fderiv, ContinuousLinearMap.comp_apply] at hc
  exact hc

omit [FiniteDimensional ℝ E] in
/-- The invariant derivative is the derivative at `0` along the curve
`t ↦ x₀ · e⁻¹(e(1) + t X)` for the extended chart `e` at the identity. -/
theorem hasDerivAt_chartCurve (u : G → ℂ) (hu : ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ u)
    (x₀ : G) (X : E) :
    HasDerivAt (fun t : ℝ => u (x₀ * (extChartAt 𝓘E (1 : G)).symm
        (extChartAt 𝓘E (1 : G) 1 + t • X)))
      (groupDirectionalValue 𝓘E X u x₀) 0 := by
  let e := extChartAt 𝓘E (1 : G)
  have hS : IsOpen e.target := isOpen_extChartAt_target (I := 𝓘E) (1 : G)
  have he : e 1 ∈ e.target := e.map_source (mem_extChartAt_source (1 : G))
  have he₁ : e.symm (e 1) = 1 := e.left_inv (mem_extChartAt_source (1 : G))
  let v (y : G) := u (x₀ * y)
  have hv : ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ v := hu.comp (contMDiff_const.mul contMDiff_id)
  have hsymm : ContMDiffAt 𝓘E 𝓘E ∞ (e.symm : E → G) (e 1) :=
    (contMDiffOn_extChartAt_symm (I := 𝓘E) (n := ∞) (1 : G) (e 1) he).contMDiffAt
      (hS.mem_nhds he)
  have hcomp : ContMDiffAt 𝓘E 𝓘(ℝ, ℂ) ∞ (v ∘ e.symm) (e 1) :=
    (hv.contMDiffAt.comp_of_eq hsymm he₁)
  have hdiff : DifferentiableAt ℝ (v ∘ e.symm) (e 1) :=
    (contMDiffAt_iff_contDiffAt.mp hcomp).differentiableAt (by simp)
  have hline : HasDerivAt (fun t : ℝ => e 1 + t • X) ((1 : ℝ) • X) 0 :=
    ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (e 1)
  have h := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  rw [one_smul] at h
  have hval := fderiv_chart_leftTranslate u hu x₀ X
  change fderiv ℝ (v ∘ e.symm) (e 1) X = _ at hval
  rw [hval] at h
  exact h

omit [FiniteDimensional ℝ E] in
/-- Measurability in a parameter passes to invariant derivatives: the derivative is a pointwise
limit of difference quotients along a smooth curve. -/
theorem aestronglyMeasurable_groupDirectionalValue {u : Ω → G → ℂ}
    (hs : ∀ x, ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ (u x))
    (hmeas : ∀ g, AEStronglyMeasurable (fun x => u x g) μ)
    (X : E) (x₀ : G) :
    AEStronglyMeasurable (fun x => groupDirectionalValue 𝓘E X (u x) x₀) μ := by
  let e := extChartAt 𝓘E (1 : G)
  let c (t : ℝ) : G := x₀ * e.symm (e 1 + t • X)
  let q (n : ℕ) (x : Ω) : ℂ := slope (fun t => u x (c t)) 0 (1 / ((n : ℝ) + 1))
  have hq (n : ℕ) : AEStronglyMeasurable (q n) μ := by
    simp only [q, slope_def_module]
    exact ((hmeas _).sub (hmeas _)).const_smul _
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => by
        simp only [mem_compl_iff, mem_singleton_iff, one_div, inv_eq_zero]
        positivity⟩
  refine aestronglyMeasurable_of_tendsto_ae atTop hq (Eventually.of_forall fun x => ?_)
  exact (hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_chartCurve (u x) (hs x) x₀ X)).comp hlim

omit [FiniteDimensional ℝ E] [Group G] [LieGroup 𝓘(ℝ, E) ∞ G] in
private theorem integrable_of_dominated
    (hmeas : ∀ a g, AEStronglyMeasurable (fun x => f a x g) μ)
    (hdom : ∀ a (g₀ : G), ∃ U ∈ 𝓝 g₀, ∃ bound : Ω → ℝ, Integrable bound μ ∧
      ∀ x, ∀ g ∈ U, ‖f a x g‖ ≤ bound x) (a : A) (g : G) :
    Integrable (fun x => f a x g) μ := by
  obtain ⟨U, hU, bd, hbd, hle⟩ := hdom a g
  exact hbd.mono' (hmeas a g) (Eventually.of_forall fun x => hle x g (mem_of_mem_nhds hU))

omit [FiniteDimensional ℝ E] [LieGroup 𝓘(ℝ, E) ∞ G] in
set_option maxHeartbeats 1000000 in
/-- In a chart with an invariant derivative expansion, the integral has the expanded
derivative, with the integrals of the differentiated integrands as coefficients. -/
private theorem hasFDerivAt_integral_of_expansion
    (step : GroupLieAlgebra 𝓘E G → A → A)
    (hs : ∀ a x, ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ (f a x))
    (hder : ∀ a x X, groupDirectionalValue 𝓘E X (f a x) = f (step X a) x)
    (hmeas : ∀ a g, AEStronglyMeasurable (fun x => f a x g) μ)
    (hdom : ∀ a (g₀ : G), ∃ U ∈ 𝓝 g₀, ∃ bound : Ω → ℝ, Integrable bound μ ∧
      ∀ x, ∀ g ∈ U, ‖f a x g‖ ≤ bound x)
    (ψ : E → G) {S : Set E} (hS : IsOpen S) (hψ : ContMDiffOn 𝓘E 𝓘E ∞ ψ S)
    (X : J → GroupLieAlgebra 𝓘E G) (L : J → E → E →L[ℝ] ℝ)
    (hL : ∀ j, ContDiffOn ℝ ∞ (L j) S)
    (hexp : ∀ (u : G → ℂ), ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ u → ∀ y ∈ S,
      HasFDerivAt (u ∘ ψ) (∑ j, (L j y).smulRight (groupDirectionalValue 𝓘E (X j) u (ψ y))) y)
    (a : A) (y₀ : E) (hy₀ : y₀ ∈ S) :
    HasFDerivAt ((fun g => ∫ x, f a x g ∂μ) ∘ ψ)
      (invariantCoordinateDerivative (fun j => L j y₀)
        (fun j => ∫ x, f (step (X j) a) x (ψ y₀) ∂μ)) y₀ := by
  have hint := integrable_of_dominated hmeas hdom
  choose U hU bd hbd hle using fun j : J => hdom (step (X j) a) (ψ y₀)
  let F' : E → Ω → E →L[ℝ] ℂ := fun y x =>
    ∑ j, (L j y).smulRight (f (step (X j) a) x (ψ y))
  have hψc : ContinuousAt ψ y₀ := hψ.continuousOn.continuousAt (hS.mem_nhds hy₀)
  have hLc (j : J) : ContinuousAt (L j) y₀ :=
    (hL j).continuousOn.continuousAt (hS.mem_nhds hy₀)
  let s : Set E := (S ∩ ψ ⁻¹' (⋂ j, U j)) ∩ ⋂ j, {y | ‖L j y‖ < ‖L j y₀‖ + 1}
  have hsN : s ∈ 𝓝 y₀ := by
    refine inter_mem (inter_mem (hS.mem_nhds hy₀) (hψc.preimage_mem_nhds ?_)) ?_
    · exact iInter_mem.mpr fun j => hU j
    · exact iInter_mem.mpr fun j =>
        (hLc j).norm.eventually (gt_mem_nhds (lt_add_one _))
  let bound : Ω → ℝ := fun x => ∑ j, (‖L j y₀‖ + 1) * bd j x
  have hsmul (c : E →L[ℝ] ℝ) (v : ℂ) :
      ContinuousLinearMap.smulRightL ℝ E ℂ c v = c.smulRight v := rfl
  have hterm (j : J) : Integrable
      (fun x => (L j y₀).smulRight (f (step (X j) a) x (ψ y₀))) μ := by
    have h := (ContinuousLinearMap.smulRightL ℝ E ℂ (L j y₀)).integrable_comp
      (hint (step (X j) a) (ψ y₀))
    simp only [hsmul] at h
    exact h
  have hF'int : Integrable
      (fun x => ∑ j, (L j y₀).smulRight (f (step (X j) a) x (ψ y₀))) μ :=
    integrable_finsetSum (f := fun j x => (L j y₀).smulRight (f (step (X j) a) x (ψ y₀)))
      Finset.univ fun j _ => hterm j
  have hF'meas : AEStronglyMeasurable (F' y₀) μ := hF'int.aestronglyMeasurable
  have h_bound : ∀ᵐ x ∂μ, ∀ y ∈ s, ‖F' y x‖ ≤ bound x := by
    refine Eventually.of_forall fun x y hy => ?_
    have hy1 : ∀ j, ‖L j y‖ ≤ ‖L j y₀‖ + 1 := fun j => (mem_iInter.mp hy.2 j).le
    have hy2 : ∀ j, ψ y ∈ U j := fun j => mem_iInter.mp hy.1.2 j
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul (hy1 j) (hle j x (ψ y) (hy2 j)) (norm_nonneg _)
      (add_nonneg (norm_nonneg _) zero_le_one)
  have hbint : Integrable bound μ :=
    integrable_finsetSum (f := fun j x => (‖L j y₀‖ + 1) * bd j x) Finset.univ
      fun j _ => (hbd j).const_mul _
  have h_diff : ∀ᵐ x ∂μ, ∀ y ∈ s, HasFDerivAt (fun y => f a x (ψ y)) (F' y x) y := by
    refine Eventually.of_forall fun x y hy => ?_
    have h := hexp (f a x) (hs a x) y hy.1.1
    simp only [hder] at h
    exact h
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y x => f a x (ψ y)) (F' := F') (bound := bound) hsN
    (Eventually.of_forall fun y => hmeas a (ψ y)) (hint a (ψ y₀)) hF'meas h_bound hbint h_diff
  have hval : ∫ x, F' y₀ x ∂μ = invariantCoordinateDerivative (fun j => L j y₀)
      (fun j => ∫ x, f (step (X j) a) x (ψ y₀) ∂μ) := by
    change ∫ x, ∑ j, (L j y₀).smulRight (f (step (X j) a) x (ψ y₀)) ∂μ = _
    rw [integral_finsetSum _ fun j _ => hterm j]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h := (ContinuousLinearMap.smulRightL ℝ E ℂ (L j y₀)).integral_comp_comm
      (hint (step (X j) a) (ψ y₀))
    simp only [hsmul] at h
    exact h
  rw [← hval]
  exact key

/-- Differentiation under the integral sign on a Lie group. If the integrands are smooth,
closed under invariant differentiation through `step`, measurable in the integration variable
and locally uniformly dominated by integrable functions, then every integral is smooth and its
invariant derivatives are the integrals of the invariant derivatives. -/
theorem contMDiff_integral_of_dominated_invariantDerivatives
    (step : GroupLieAlgebra 𝓘E G → A → A)
    (hs : ∀ a x, ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ (f a x))
    (hder : ∀ a x X, groupDirectionalValue 𝓘E X (f a x) = f (step X a) x)
    (hmeas : ∀ a g, AEStronglyMeasurable (fun x => f a x g) μ)
    (hdom : ∀ a (g₀ : G), ∃ U ∈ 𝓝 g₀, ∃ bound : Ω → ℝ, Integrable bound μ ∧
      ∀ x, ∀ g ∈ U, ‖f a x g‖ ≤ bound x) :
    (∀ a, ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ (fun g => ∫ x, f a x g ∂μ)) ∧
      ∀ a X, groupDirectionalValue 𝓘E X (fun g => ∫ x, f a x g ∂μ) =
        fun g => ∫ x, f (step X a) x g ∂μ := by
  let g (a : A) (z : G) : ℂ := ∫ x, f a x z ∂μ
  have hCD (n : ℕ) {S : Set E} (hS : IsOpen S) (ψ : E → G)
      (hψ : ContMDiffOn 𝓘E 𝓘E ∞ ψ S) :
      ∀ a, ContDiffOn ℝ n (g a ∘ ψ) S := by
    obtain ⟨X, L, hL, hexp⟩ := exists_invariantDerivativeExpansion ψ hS hψ
    have hD := hasFDerivAt_integral_of_expansion step hs hder hmeas hdom ψ hS hψ X L hL hexp
    induction n with
    | zero =>
      intro a
      rw [Nat.cast_zero, contDiffOn_zero]
      exact fun y hy => (hD a y hy).continuousAt.continuousWithinAt
    | succ n ih =>
      intro a
      let D (y : E) : E →L[ℝ] ℂ := ∑ j, (L j y).smulRight (g (step (X j) a) (ψ y))
      rw [Nat.cast_succ, contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hS.uniqueDiffOn]
      refine ⟨fun h => ((show (n : ℕ∞ω) ≠ ω by simp) h).elim, D, ?_, fun y hy =>
        (hD a y hy).hasFDerivWithinAt⟩
      apply ContDiffOn.sum
      intro j _
      exact ((hL j).of_le (by simp)).smulRight (ih (step (X j) a))
  have hg (a : A) : ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ (g a) := by
    intro x
    let e := extChartAt 𝓘E x
    have hx : e x ∈ e.target := e.map_source (mem_extChartAt_source x)
    rw [contMDiffAt_iff_source, ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ,
      contMDiffAt_iff_contDiffAt]
    refine (contDiffOn_infty.mpr (fun n => hCD n (isOpen_extChartAt_target (I := 𝓘E) x)
      e.symm (contMDiffOn_extChartAt_symm x) a) (e x) hx).contDiffAt ?_
    exact (isOpen_extChartAt_target (I := 𝓘E) x).mem_nhds hx
  refine ⟨hg, fun a X => ?_⟩
  funext x₀
  let e := extChartAt 𝓘E (1 : G)
  let ψ (y : E) := x₀ * e.symm y
  have hS : IsOpen e.target := isOpen_extChartAt_target (I := 𝓘E) (1 : G)
  have he : e 1 ∈ e.target := e.map_source (mem_extChartAt_source (1 : G))
  have he₁ : e.symm (e 1) = 1 := e.left_inv (mem_extChartAt_source (1 : G))
  have hψ : ContMDiffOn 𝓘E 𝓘E ∞ ψ e.target :=
    contMDiffOn_const.mul (contMDiffOn_extChartAt_symm (1 : G))
  have hψ₁ : ψ (e 1) = x₀ := by simp only [ψ, he₁, mul_one]
  obtain ⟨Y, L, hL, hexp⟩ := exists_invariantDerivativeExpansion ψ hS hψ
  have hD := hasFDerivAt_integral_of_expansion step hs hder hmeas hdom ψ hS hψ Y L hL hexp
  have htrans (u : G → ℂ) (hu : ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ u) :
      fderiv ℝ (u ∘ ψ) (e 1) X = groupDirectionalValue 𝓘E X u x₀ :=
    fderiv_chart_leftTranslate u hu x₀ X
  have hpt (x : Ω) :
      f (step X a) x x₀ = ∑ j, (L j (e 1)) X • f (step (Y j) a) x x₀ := by
    have h1 := htrans (f a x) (hs a x)
    rw [(hexp (f a x) (hs a x) (e 1) he).fderiv, hder, hψ₁] at h1
    simpa only [_root_.sum_apply, ContinuousLinearMap.smulRight_apply, hder,
      hψ₁] using h1.symm
  have hint := integrable_of_dominated hmeas hdom
  rw [← htrans (g a) (hg a), (hD a (e 1) he).fderiv]
  change (∑ j, (L j (e 1)).smulRight (∫ x, f (step (Y j) a) x (ψ (e 1)) ∂μ)) (X : E) =
    ∫ x, f (step X a) x x₀ ∂μ
  rw [hψ₁, integral_congr_ae (Eventually.of_forall hpt),
    integral_finsetSum (f := fun j x => (L j (e 1)) (X : E) • f (step (Y j) a) x x₀)
      Finset.univ fun j _ => (hint (step (Y j) a) x₀).smul ((L j (e 1)) (X : E))]
  simp only [_root_.sum_apply, ContinuousLinearMap.smulRight_apply, integral_smul]

end Langlands.Geometry.Manifold
