import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences

/-! # Continuity of integrable scalar kernels on barrelled spaces -/

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal

set_option autoImplicit false

namespace Langlands.Analysis

variable {X V : Type*} [MeasurableSpace X] [AddCommGroup V] [Module ℂ V]
  [TopologicalSpace V]

/-- A pointwise continuous linear kernel integrable on every vector has a continuous integral
of its norm and a continuous linear scalar integral. -/
def IntegrableLinearKernelContinuityStatement (μ : Measure X) (K : X → V →L[ℂ] ℂ) : Prop :=
  ∀ [IsTopologicalAddGroup V] [SequentialSpace V] [BarrelledSpace ℂ V],
    (∀ v, Integrable (fun x => K x v) μ) →
    (∃ p : Seminorm ℂ V, Continuous p ∧ ∀ v, p v = ∫ x, ‖K x v‖ ∂μ) ∧
    ∃ I : V →L[ℂ] ℂ, ∀ v, I v = ∫ x, K x v ∂μ

theorem integrableLinearKernelContinuity (μ : Measure X) (K : X → V →L[ℂ] ℂ) :
    IntegrableLinearKernelContinuityStatement μ K := by
  intro _ _ _ hInt
  let p : Seminorm ℂ V := Seminorm.of (fun v => ∫ x, ‖K x v‖ ∂μ)
    (fun v w => by
      rw [← integral_add (hInt v).norm (hInt w).norm]
      exact integral_mono (hInt (v + w)).norm ((hInt v).norm.add (hInt w).norm)
        (fun x => by simpa only [map_add, Pi.add_apply] using norm_add_le (K x v) (K x w)))
    (fun z v => by simp only [map_smul, norm_smul, integral_const_mul])
  have hp (v : V) : p v = ∫ x, ‖K x v‖ ∂μ := rfl
  have hpMeasure (v : V) : ENNReal.ofReal (p v) = ∫⁻ x, ‖K x v‖ₑ ∂μ :=
    ofReal_integral_norm_eq_lintegral_enorm (hInt v)
  have hpCont : Continuous p := p.continuous_of_lowerSemicontinuous (by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro c
    apply isSeqClosed_iff_isClosed.mp
    intro u v hu hv
    have hlim (x : X) : liminf (fun n => ‖K x (u n)‖ₑ) atTop = ‖K x v‖ₑ :=
      (((K x).continuous.tendsto v).comp hv).enorm.liminf_eq
    have hBound : ENNReal.ofReal (p v) ≤ ENNReal.ofReal c := calc
      _ = ∫⁻ x, ‖K x v‖ₑ ∂μ := hpMeasure v
      _ = ∫⁻ x, liminf (fun n => ‖K x (u n)‖ₑ) atTop ∂μ := lintegral_congr fun x => (hlim x).symm
      _ ≤ liminf (fun n => ∫⁻ x, ‖K x (u n)‖ₑ ∂μ) atTop :=
        lintegral_liminf_le' fun n => (hInt (u n)).aestronglyMeasurable.aemeasurable.enorm
      _ ≤ ENNReal.ofReal c := liminf_le_of_frequently_le' <| .of_forall fun n =>
        (hpMeasure (u n)).symm ▸ ENNReal.ofReal_le_ofReal (hu n)
    have hc : 0 ≤ c := (apply_nonneg p (u 0)).trans (hu 0)
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hBound
    rwa [ENNReal.toReal_ofReal (apply_nonneg p _), ENNReal.toReal_ofReal hc] at h)
  let I : V →ₗ[ℂ] ℂ :=
    { toFun := fun v => ∫ x, K x v ∂μ
      map_add' v w := by simp only [map_add, integral_add (hInt v) (hInt w)]
      map_smul' z v := by simp only [map_smul, integral_smul, RingHom.id_apply] }
  have hI : Continuous I := by
    apply continuous_of_continuousAt_zero I
    rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
    have hP : Tendsto p (𝓝 (0 : V)) (𝓝 0) := by simpa only [map_zero] using hpCont.tendsto 0
    exact squeeze_zero (fun _ => norm_nonneg _) (fun v => norm_integral_le_integral_norm _) hP
  exact ⟨⟨p, hpCont, hp⟩, ⟨⟨I, hI⟩, fun _ => rfl⟩⟩

end Langlands.Analysis
