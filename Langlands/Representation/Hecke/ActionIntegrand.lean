import Langlands.HarmonicAnalysis.Basic
import Langlands.HarmonicAnalysis.AlgebraicIntegrand
import Langlands.Representation.Smooth.FixedVectors.Definitions

/-! Actual finite-image integrands for the positive-convention Hecke action. -/

noncomputable section

namespace Langlands.Hecke

open HarmonicAnalysis MeasureTheory

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A smooth vector's positive orbit map is locally constant. No topology on the
representation carrier is involved. -/
theorem orbitMap_locallyConstant (ρ : Representation ℂ G V) {v : V}
    (hv : IsSmoothVector ρ v) : IsLocallyConstant (fun g => ρ g v) := by
  obtain ⟨K, hK⟩ := hv
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro g
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' (K : Set G),
    K.isOpen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp
  · intro x hx
    have hfix : ρ (g⁻¹ * x) v = v := hK ⟨g⁻¹ * x, hx⟩
    calc
      ρ x v = ρ g (ρ (g⁻¹ * x) v) := by
        rw [← Module.End.mul_apply, ← map_mul]
        simp
      _ = ρ g v := congrArg (ρ g) hfix

variable [MeasurableSpace G] [OpensMeasurableSpace G]

/-- The Hecke action integrand `g ↦ f(g) • ρ(g)v` as an actual simple function.
The Schwartz–Bruhat space is the existing carrier of Hecke test functions. -/
def actionIntegrand (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (f : SchwartzBruhat G) (v : V) : SimpleFunc G V :=
  compactlySupportedSimpleFunc (fun g => f g • ρ g v)
    (f.locallyConstant.comp₂ (orbitMap_locallyConstant ρ (hρ v)) (· • ·))
    f.hasCompactSupport.smul_right

@[simp]
theorem actionIntegrand_apply (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (f : SchwartzBruhat G) (v : V) (g : G) :
    actionIntegrand ρ hρ f v g = f g • ρ g v := rfl

theorem actionIntegrand_finMeasSupp
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (f : SchwartzBruhat G) (v : V) :
    (actionIntegrand ρ hρ f v).FinMeasSupp μ :=
  compactlySupportedSimpleFunc_finMeasSupp μ _ _ _

/-- The action integrand is complex bilinear before integration. -/
def actionIntegrandLinear (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) :
    SchwartzBruhat G →ₗ[ℂ] V →ₗ[ℂ] SimpleFunc G V where
  toFun f :=
    { toFun := actionIntegrand ρ hρ f
      map_add' := by
        intro v w
        ext g
        simp [smul_add]
      map_smul' := by
        intro c v
        ext g
        simp [smul_smul, mul_comm] }
  map_add' := by
    intro f h
    ext v g
    change (f g + h g) • ρ g v = f g • ρ g v + h g • ρ g v
    exact add_smul _ _ _
  map_smul' := by
    intro c f
    ext v g
    change (c • f g) • ρ g v = c • (f g • ρ g v)
    exact mul_smul c (f g) (ρ g v)

@[simp]
theorem actionIntegrandLinear_apply (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (f : SchwartzBruhat G) (v : V) :
    actionIntegrandLinear ρ hρ f v = actionIntegrand ρ hρ f v := rfl

/-- Intertwiners carry the actual integrands to the corresponding integrands. -/
theorem actionIntegrand_intertwiner
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (T : ρ.IntertwiningMap σ)
    (f : SchwartzBruhat G) (v : V) :
    (actionIntegrand ρ hρ f v).map T = actionIntegrand σ hσ f (T v) := by
  ext g
  simp only [SimpleFunc.map_apply, actionIntegrand_apply, map_smul]
  rw [T.isIntertwining]

end Langlands.Hecke
