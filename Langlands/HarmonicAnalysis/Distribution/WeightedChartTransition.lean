import Langlands.HarmonicAnalysis.Distribution.NormalizedChartDistribution
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-! # Weighted transition of a Jacobian-normalized chart distribution -/

noncomputable section

open Function Set TopologicalSpace Filter
open scoped ContDiff Distributions Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.HarmonicAnalysis

variable {E X F : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The local coordinate expression of an ambient continuous linear equivalence. -/
def chartLinearTransition (e : OpenPartialHomeomorph E X) (A : X ≃L[ℝ] X) :
    OpenPartialHomeomorph E E :=
  (e.transHomeomorph A.toHomeomorph).trans e.symm

@[simp]
theorem chartLinearTransition_apply (e : OpenPartialHomeomorph E X) (A : X ≃L[ℝ] X) (x : E) :
    chartLinearTransition e A x = e.symm (A (e x)) := rfl

@[simp]
theorem mem_chartLinearTransition_source (e : OpenPartialHomeomorph E X) (A : X ≃L[ℝ] X) (x : E) :
    x ∈ (chartLinearTransition e A).source ↔ x ∈ e.source ∧ A (e x) ∈ e.target := by
  rw [chartLinearTransition, OpenPartialHomeomorph.trans_source]
  rfl

@[simp]
theorem mem_chartLinearTransition_target (e : OpenPartialHomeomorph E X) (A : X ≃L[ℝ] X) (x : E) :
    x ∈ (chartLinearTransition e A).target ↔ x ∈ e.source ∧ A.symm (e x) ∈ e.target := by
  rw [chartLinearTransition, OpenPartialHomeomorph.trans_target]
  rfl

@[simp]
theorem chartLinearTransition_symm_apply (e : OpenPartialHomeomorph E X) (A : X ≃L[ℝ] X) (x : E) :
    (chartLinearTransition e A).symm x = e.symm (A.symm (e x)) := rfl

variable [NormedSpace ℝ E]
variable {e : OpenPartialHomeomorph E X} (he : ContDiffOn ℝ ∞ e e.source)
  (hei : ContDiffOn ℝ ∞ e.symm e.target) (A : X ≃L[ℝ] X)

include he hei in
theorem contDiffOn_chartLinearTransition :
    ContDiffOn ℝ ∞ (chartLinearTransition e A) (chartLinearTransition e A).source := by
  have hs (x : E) (hx : x ∈ (chartLinearTransition e A).source) :=
    (mem_chartLinearTransition_source e A x).mp hx
  have h : ContDiffOn ℝ ∞ (fun x => A (e x)) (chartLinearTransition e A).source :=
    A.contDiff.contDiffOn.comp (he.mono fun x hx => (hs x hx).1) (fun _ _ => mem_univ _)
  exact hei.comp h (fun x hx => (hs x hx).2)

include he hei in
theorem contDiffOn_chartLinearTransition_symm :
    ContDiffOn ℝ ∞ (chartLinearTransition e A).symm (chartLinearTransition e A).target := by
  have h : (chartLinearTransition e A).target = (chartLinearTransition e A.symm).source := by
    ext x
    simp
  rw [h]
  exact contDiffOn_chartLinearTransition he hei A.symm

include he hei in
/-- The Jacobian of a coordinate transition associated to a volume-preserving ambient linear map. -/
theorem chartAbsJacobian_mul_chartLinearTransition (L : E ≃L[ℝ] X)
    (hA : |A.toContinuousLinearMap.det| = 1)
    {x : E} (hx : x ∈ (chartLinearTransition e A).source) :
    chartAbsJacobian L e (chartLinearTransition e A x) *
      chartAbsJacobian (ContinuousLinearEquiv.refl ℝ E) (chartLinearTransition e A) x =
      chartAbsJacobian L e x := by
  let Ψ := chartLinearTransition e A
  have hx' := (mem_chartLinearTransition_source e A x).mp hx
  have hψ := (contDiffOn_chartLinearTransition he hei A).contDiffAt (Ψ.open_source.mem_nhds hx)
  have he' := he.contDiffAt (e.open_source.mem_nhds hx'.1)
  have hψx : Ψ x ∈ e.source := e.map_target hx'.2
  have heψ := he.contDiffAt (e.open_source.mem_nhds hψx)
  have heq : (fun y => A (e y)) =ᶠ[𝓝 x] e ∘ Ψ := by
    filter_upwards [Ψ.open_source.mem_nhds hx] with y hy
    exact (e.right_inv ((mem_chartLinearTransition_source e A y).mp hy).2).symm
  let Dx := fderiv ℝ e x
  let Dy := fderiv ℝ e (Ψ x)
  let Dψ := fderiv ℝ Ψ x
  have hd : Dy.comp Dψ = A.toContinuousLinearMap.comp Dx := by
    exact ((heψ.differentiableAt (by simp)).hasFDerivAt.comp x
      (hψ.differentiableAt (by simp)).hasFDerivAt).congr_of_eventuallyEq heq |>.unique
        (A.toContinuousLinearMap.hasFDerivAt.comp x (he'.differentiableAt (by simp)).hasFDerivAt)
  let B : E →ₗ[ℝ] E := L.symm.toLinearEquiv.conj A.toLinearEquiv.toLinearMap
  have hd' : (L.symm.toContinuousLinearMap.comp Dy).toLinearMap.comp Dψ.toLinearMap =
      B.comp (L.symm.toContinuousLinearMap.comp Dx).toLinearMap := by
    ext1 v
    change L.symm (Dy (Dψ v)) = L.symm (A (L (L.symm (Dx v))))
    rw [L.apply_symm_apply]
    exact congrArg L.symm (DFunLike.congr_fun hd v)
  have hB : LinearMap.det B = A.toContinuousLinearMap.det := by
    change LinearMap.det (L.symm.toLinearEquiv.toLinearMap ∘ₗ A.toLinearEquiv.toLinearMap ∘ₗ
      L.symm.toLinearEquiv.symm.toLinearMap) = LinearMap.det A.toLinearEquiv.toLinearMap
    exact LinearMap.det_conj _ _
  have hj := congrArg (fun m : E →ₗ[ℝ] E => |LinearMap.det m|) hd'
  simp only [LinearMap.det_comp, abs_mul, hB, hA, one_mul] at hj
  change |(L.symm.toContinuousLinearMap.comp Dy).det| *
      |((ContinuousLinearEquiv.refl ℝ E).symm.toContinuousLinearMap.comp Dψ).det| =
        |(L.symm.toContinuousLinearMap.comp Dx).det|
  have hrefl : (ContinuousLinearEquiv.refl ℝ E).symm.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ E := rfl
  rw [hrefl, ContinuousLinearMap.id_comp]
  exact hj

/-- The transition restricted by an open condition on its source. -/
abbrev chartLinearTransitionOn (e : OpenPartialHomeomorph E X) (A : X ≃L[ℝ] X) (U : Opens E) :
    OpenPartialHomeomorph E E := (chartLinearTransition e A).restrOpen U U.isOpen

omit [NormedSpace ℝ E] in
theorem chartLinearTransition_source_le : chartSource (chartLinearTransition e A) ≤ chartSource e :=
  fun x hx => ((mem_chartLinearTransition_source e A x).mp hx).1

omit [NormedSpace ℝ E] in
theorem chartLinearTransitionOn_target_le (U : Opens E) :
    chartTarget (chartLinearTransitionOn e A U) ≤ chartSource e :=
  fun x hx => ((mem_chartLinearTransition_target e A x).mp hx.1).1

include he hei in
theorem contDiffOn_chartLinearTransitionOn (U : Opens E) :
    ContDiffOn ℝ ∞ (chartLinearTransitionOn e A U) (chartLinearTransitionOn e A U).source :=
  (contDiffOn_chartLinearTransition he hei A).mono (fun _ hx => hx.1)

/-- Ordinary pullback by the chart transition on a chosen source open set, after extending the
target test into the transition image. -/
def chartLinearTransitionPullbackCLM (U V : Opens E) : 𝓓(V, ℝ) →L[ℝ] 𝓓(U, ℝ) :=
  (TestFunction.monoCLM ℝ).comp
    ((pullbackChartTestCLM (chartLinearTransitionOn e A U)
      (contDiffOn_chartLinearTransitionOn he hei A U)).comp (TestFunction.monoCLM ℝ))

variable {U V : Opens E}
  (hU : U ≤ chartSource (chartLinearTransition e A))
  (hV : V ≤ chartTarget (chartLinearTransitionOn e A U))

include hU hV in
theorem chartLinearTransitionPullbackCLM_apply_of_mem (f : 𝓓(V, ℝ)) {x : E} (hx : x ∈ U) :
    chartLinearTransitionPullbackCLM he hei A U V f x = f (chartLinearTransition e A x) := by
  let r := chartLinearTransitionOn e A U
  have hSource : chartSource r ≤ U := fun _ h => h.2
  have hx' : x ∈ r.source := ⟨hU hx, hx⟩
  let g : 𝓓(chartTarget r, ℝ) := TestFunction.monoCLM ℝ f
  have hVr : V ≤ chartTarget r := hV
  have hg : (g : E → ℝ) = f := by simp [g, hVr]
  let p := pullbackChartTestCLM r (contDiffOn_chartLinearTransitionOn he hei A U) g
  have hp : ((TestFunction.monoCLM ℝ p : 𝓓(U, ℝ)) : E → ℝ) = p := by simp [hSource]
  change (TestFunction.monoCLM ℝ p : 𝓓(U, ℝ)) x = f (chartLinearTransition e A x)
  rw [congrFun hp, pullbackChartTestCLM_apply_of_mem r _ g hx', congrFun hg]
  rfl

variable [FiniteDimensional ℝ E]

include he hei hU in
private theorem contDiffOn_chartLinearTransitionAbsJacobian :
    ContDiffOn ℝ ∞ (chartAbsJacobian (ContinuousLinearEquiv.refl ℝ E) (chartLinearTransition e A)) U :=
  (contDiffOn_chartAbsJacobian (contDiffOn_chartLinearTransition he hei A)
    (contDiffOn_chartLinearTransition_symm he hei A) (ContinuousLinearEquiv.refl ℝ E)).mono hU

/-- Pull back a target test in the chosen coordinate opens and multiply by the absolute
Jacobian of the transition on the source. -/
def weightedChartLinearTransitionPullbackCLM (V : Opens E) : 𝓓(V, ℝ) →L[ℝ] 𝓓(U, ℝ) :=
  (localScalarMultiplierCLM (contDiffOn_chartLinearTransitionAbsJacobian he hei A hU)).comp
    (chartLinearTransitionPullbackCLM he hei A U V)

include hU hV in
theorem weightedChartLinearTransitionPullbackCLM_apply_of_mem (f : 𝓓(V, ℝ)) {x : E} (hx : x ∈ U) :
    weightedChartLinearTransitionPullbackCLM he hei A hU V f x =
      f (chartLinearTransition e A x) *
        chartAbsJacobian (ContinuousLinearEquiv.refl ℝ E) (chartLinearTransition e A) x := by
  rw [weightedChartLinearTransitionPullbackCLM, ContinuousLinearMap.comp_apply,
    localScalarMultiplierCLM_apply, chartLinearTransitionPullbackCLM_apply_of_mem he hei A hU hV f hx]

include hU hV in
/-- A unit-absolute-determinant ambient covariance law transports to the weighted chart
pullback between the normalized restrictions. The target open set is contained in the
transition image of the source, so the entire pulled-back support is included. -/
theorem jacobianNormalizedChartDistribution_eval_weightedTransition
    (L : E ≃L[ℝ] X) (hA : |A.toContinuousLinearMap.det| = 1)
    (D : 𝓓'((⊤ : Opens X), F)) (c : ℝ)
    (hD : ∀ g : 𝓓((⊤ : Opens X), ℝ), D (fullSmoothTestPullbackCLM A g) = c • D g)
    (f : 𝓓(V, ℝ)) :
    jacobianNormalizedChartDistribution he hei L (hU.trans (chartLinearTransition_source_le A)) D
        (weightedChartLinearTransitionPullbackCLM he hei A hU V f) =
      c • jacobianNormalizedChartDistribution he hei L
        (hV.trans (chartLinearTransitionOn_target_le A U)) D f := by
  let hUs := hU.trans (chartLinearTransition_source_le A)
  let hVs := hV.trans (chartLinearTransitionOn_target_le A U)
  let Ψ := chartLinearTransition e A
  let J := chartAbsJacobian L e
  let d := chartAbsJacobian (ContinuousLinearEquiv.refl ℝ E) Ψ
  let P := weightedChartLinearTransitionPullbackCLM he hei A hU V f
  let gV := localScalarMultiplierCLM (contDiffOn_inv_chartAbsJacobian he hei L hVs) f
  let gU := localScalarMultiplierCLM (contDiffOn_inv_chartAbsJacobian he hei L hUs) P
  let φ : 𝓓(chartSource e, ℝ) := TestFunction.monoCLM ℝ gV
  let ψ : 𝓓(chartSource e, ℝ) := TestFunction.monoCLM ℝ gU
  have hφ : (φ : E → ℝ) = gV := by simp [φ, hVs]
  have hψ : (ψ : E → ℝ) = gU := by simp [ψ, hUs]
  change chartFullDistribution e hei D ψ = c • chartFullDistribution e hei D φ
  apply chartFullDistribution_eval_of_covariance e hei e hei D A c hD ψ φ
  · intro p hp
    obtain ⟨x, hx, hxp⟩ := tsupport_chartTestToFullCLM_subset e hei φ hp
    have hxV : x ∈ V := gV.tsupport_subset (by simpa only [hφ] using hx)
    have hxt : x ∈ Ψ.target := (hV hxV).1
    have h := ((mem_chartLinearTransition_target e A x).mp hxt).2
    rw [hxp, A.symm_apply_apply] at h
    exact h
  · intro x hx
    rw [congrFun hψ, localScalarMultiplierCLM_apply]
    by_cases hxU : x ∈ U
    · have hxΨ : x ∈ Ψ.source := hU hxU
      have hxA : A (e x) ∈ e.target := ((mem_chartLinearTransition_source e A x).mp hxΨ).2
      rw [chartTestToFullCLM_apply_of_mem e hei φ hxA, congrFun hφ, localScalarMultiplierCLM_apply]
      change P x * (J x)⁻¹ = f (Ψ x) * (J (Ψ x))⁻¹
      have hp := weightedChartLinearTransitionPullbackCLM_apply_of_mem he hei A hU hV f hxU
      change P x = f (Ψ x) * d x at hp
      rw [hp]
      have hJ : J (Ψ x) * d x = J x := chartAbsJacobian_mul_chartLinearTransition he hei A L hA hxΨ
      have hy : Ψ x ∈ e.source := e.map_target hxA
      have hnx : J x ≠ 0 := (chartAbsJacobian_pos he hei L hx).ne'
      have hny : J (Ψ x) ≠ 0 := (chartAbsJacobian_pos he hei L hy).ne'
      rw [mul_assoc]
      have hd : d x * (J x)⁻¹ = (J (Ψ x))⁻¹ := by
        field_simp [hnx, hny]
        exact (mul_comm _ _).trans hJ
      rw [hd]
    · have hp : P x = 0 := P.zero_on_compl hxU
      change P x * (J x)⁻¹ = _
      rw [hp, zero_mul]
      by_cases hxA : A (e x) ∈ e.target
      · have hxΨ : x ∈ Ψ.source := (mem_chartLinearTransition_source e A x).mpr ⟨hx, hxA⟩
        have hxV : Ψ x ∉ V := by
          intro hy
          have hpre := (chartLinearTransitionOn e A U).map_target (hV hy)
          change Ψ.symm (Ψ x) ∈ Ψ.source ∩ (U : Set E) at hpre
          rw [Ψ.left_inv hxΨ] at hpre
          exact hxU hpre.2
        rw [chartTestToFullCLM_apply_of_mem e hei φ hxA, congrFun hφ]
        exact (gV.zero_on_compl hxV).symm
      · exact (chartTestToFullCLM_apply_of_notMem e hei φ hxA).symm

end Langlands.HarmonicAnalysis
