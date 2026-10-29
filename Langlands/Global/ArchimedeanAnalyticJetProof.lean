import Langlands.Global.ArchimedeanAnalyticJetStatement
import Mathlib.Analysis.Analytic.Uniqueness

/-! # Analytic uniqueness on an actual archimedean connected component -/

noncomputable section
universe u
open scoped Classical Topology Matrix.Norms.Operator
open Set Filter
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Propagate the full zero analytic matrix jet along the actual component. -/
theorem analyticMatrixJetUniqueness :
    AnalyticMatrixJetUniquenessStatement K n := by
  intro f x₀ han hjet
  let q : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K) →
      ArchimedeanMatrix K n :=
    fun x => (archimedeanGLCoordinates K n x : ArchimedeanMatrix K n)
  let S := q '' connectedComponent x₀
  have hq : Continuous q :=
    Units.continuous_val.comp (archimedeanGLCoordinates K n).continuous
  have hS : IsPreconnected S :=
    isPreconnected_connectedComponent.image q hq.continuousOn
  have hAn : AnalyticOnNhd ℝ (coordinateExtension K n f) S := by
    rintro a ⟨x, hx, rfl⟩
    exact han (archimedeanGLCoordinates K n x)
  have hbase : q x₀ ∈ S := mem_image_of_mem q mem_connectedComponent
  have hlocal : coordinateExtension K n f =ᶠ[𝓝 (q x₀)] 0 := by
    obtain ⟨p, r, hp⟩ := han (archimedeanGLCoordinates K n x₀)
    filter_upwards [Metric.eball_mem_nhds (q x₀) hp.r_pos] with y hy
    have hy' : y - q x₀ ∈ Metric.eball 0 r := by
      simpa [edist_eq_enorm_sub] using hy
    have hs : HasSum (fun _ : ℕ => (0 : ℂ)) (coordinateExtension K n f y) := by
      simpa only [q, hjet, zero_apply, smul_zero,
        add_sub_cancel] using hp.hasSum_iteratedFDeriv hy'
    exact hs.unique hasSum_zero
  have hzero := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero hS hbase hlocal
  intro x hx
  simpa only [q, coordinateExtension_apply, ContinuousMulEquiv.symm_apply_apply,
    Pi.zero_apply] using hzero (mem_image_of_mem q hx)

end Langlands.Global.ArchimedeanGL
