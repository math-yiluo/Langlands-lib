import Langlands.Representation.CompactSchurAveragingStatement
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Schur averaging by finite-dimensional integration and trace -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Representation.CompactSchur

open MeasureTheory
open scoped BigOperators

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {d : ℕ} (ρ : _root_.Representation ℂ G (Fin d → ℂ))
  (hρ : Continuous (fun p : G × (Fin d → ℂ) => ρ p.1 p.2))
  (ν : Measure G) [IsFiniteMeasure ν]

include hρ in
omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
theorem continuous_conjugate (T : Module.End ℂ (Fin d → ℂ)) (v : Fin d → ℂ) :
    Continuous (fun k : G => ρ k (T (ρ k⁻¹ v))) := by
  have hi : Continuous (fun k : G => ρ k⁻¹ v) :=
    hρ.comp (continuous_inv.prodMk continuous_const)
  exact hρ.comp (continuous_id.prodMk (T.continuous_of_finiteDimensional.comp hi))

include hρ in
theorem integrable_conjugate (T : Module.End ℂ (Fin d → ℂ)) (v : Fin d → ℂ) :
    Integrable (fun k : G => ρ k (T (ρ k⁻¹ v))) ν :=
  (continuous_conjugate ρ hρ T v).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The average of the conjugates, constructed in a finite-dimensional Banach space. -/
def averageEnd (T : Module.End ℂ (Fin d → ℂ)) : Module.End ℂ (Fin d → ℂ) where
  toFun v := ∫ k : G, ρ k (T (ρ k⁻¹ v)) ∂ν
  map_add' v w := by
    simp only [map_add]
    exact integral_add (integrable_conjugate ρ hρ ν T v)
      (integrable_conjugate ρ hρ ν T w)
  map_smul' c v := by
    simp only [map_smul, RingHom.id_apply]
    exact integral_smul c _

theorem averageEnd_intertwines [ν.IsMulLeftInvariant]
    (T : Module.End ℂ (Fin d → ℂ)) (h : G) (v : Fin d → ℂ) :
    averageEnd ρ hρ ν T (ρ h v) = ρ h (averageEnd ρ hρ ν T v) := by
  change (∫ k : G, ρ k (T (ρ k⁻¹ (ρ h v))) ∂ν) =
    ρ h (∫ k : G, ρ k (T (ρ k⁻¹ v)) ∂ν)
  have hL := (ρ h).toContinuousLinearMap.integral_comp_comm
    (integrable_conjugate ρ hρ ν T v)
  change (∫ k : G, ρ h (ρ k (T (ρ k⁻¹ v))) ∂ν) =
    ρ h (∫ k : G, ρ k (T (ρ k⁻¹ v)) ∂ν) at hL
  rw [← hL]
  have hi := integral_mul_left_eq_self (μ := ν)
    (fun k : G => ρ k (T (ρ k⁻¹ (ρ h v)))) h
  rw [← hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro k
  simp only [mul_inv_rev, map_mul, Module.End.mul_apply, _root_.Representation.inv_self_apply]

def averageIntertwiner [ν.IsMulLeftInvariant]
    (T : Module.End ℂ (Fin d → ℂ)) : ρ.IntertwiningMap ρ :=
  (averageEnd ρ hρ ν T).intertwiningMap_of_isIntertwiningMap ρ ρ
    (averageEnd_intertwines ρ hρ ν T)

theorem averageEnd_scalar [ν.IsMulLeftInvariant] [ρ.IsIrreducible]
    (T : Module.End ℂ (Fin d → ℂ)) :
    ∃ c : ℂ, ∀ v, averageEnd ρ hρ ν T v = c • v := by
  obtain ⟨c, hc⟩ :=
    (_root_.Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).2 (averageIntertwiner ρ hρ ν T)
  refine ⟨c, fun v => ?_⟩
  have hv := congrArg (fun L : ρ.IntertwiningMap ρ => L v) hc
  change c • v = averageEnd ρ hρ ν T v at hv
  exact hv.symm

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] in
theorem trace_conjugate (T : Module.End ℂ (Fin d → ℂ)) (k : G) :
    Matrix.trace (LinearMap.toMatrix' (ρ k * T * ρ k⁻¹)) =
      Matrix.trace (LinearMap.toMatrix' T) := by
  have hm : LinearMap.toMatrix' (ρ k⁻¹) * LinearMap.toMatrix' (ρ k) = 1 := by
    rw [← LinearMap.toMatrix'_mul, ← map_mul, inv_mul_cancel, map_one,
      LinearMap.toMatrix'_one]
  rw [LinearMap.toMatrix'_mul, LinearMap.toMatrix'_mul, Matrix.trace_mul_cycle, hm,
    Matrix.one_mul]

theorem trace_averageEnd [IsProbabilityMeasure ν]
    (T : Module.End ℂ (Fin d → ℂ)) :
    Matrix.trace (LinearMap.toMatrix' (averageEnd ρ hρ ν T)) =
      Matrix.trace (LinearMap.toMatrix' T) := by
  have heval (i : Fin d) :
      (∫ k : G, ρ k (T (ρ k⁻¹ (Pi.single i 1))) ∂ν) i =
        ∫ k : G, ρ k (T (ρ k⁻¹ (Pi.single i 1))) i ∂ν := by
    exact ((ContinuousLinearMap.proj i : (Fin d → ℂ) →L[ℂ] ℂ).integral_comp_comm
      (integrable_conjugate ρ hρ ν T (Pi.single i 1))).symm
  have hint (i : Fin d) :
      Integrable (fun k : G => ρ k (T (ρ k⁻¹ (Pi.single i 1))) i) ν := by
    have hc := (continuous_apply i).comp
      (continuous_conjugate ρ hρ T (Pi.single i 1))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∑ i : Fin d,
    (∫ k : G, ρ k (T (ρ k⁻¹ (Pi.single i 1))) ∂ν) i) = _
  simp_rw [heval]
  rw [← integral_finsetSum Finset.univ (fun i _ => hint i)]
  have ht (k : G) :
      (∑ i : Fin d, ρ k (T (ρ k⁻¹ (Pi.single i 1))) i) =
        Matrix.trace (LinearMap.toMatrix' T) := by
    simpa only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix'_apply,
      Module.End.mul_apply] using
      trace_conjugate ρ T k
  simp_rw [ht]
  simp

end Langlands.Representation.CompactSchur

namespace Langlands.Representation

open CompactSchur

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

theorem compactSchurAveraging : CompactSchurAveragingStatement G := by
  intro d ρ hρ hirr ν _ _
  have : ρ.IsIrreducible := hirr
  intro T v
  obtain ⟨c, hc⟩ := averageEnd_scalar ρ hρ ν T
  have heq : averageEnd ρ hρ ν T = c • (1 : Module.End ℂ (Fin d → ℂ)) := by
    apply LinearMap.ext
    intro w
    exact hc w
  have ht := trace_averageEnd ρ hρ ν T
  rw [heq] at ht
  simp only [map_smul, LinearMap.toMatrix'_one, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul] at ht
  change (d : ℂ) • averageEnd ρ hρ ν T v = _
  rw [hc, smul_smul, mul_comm (d : ℂ) c, ht]

end Langlands.Representation
