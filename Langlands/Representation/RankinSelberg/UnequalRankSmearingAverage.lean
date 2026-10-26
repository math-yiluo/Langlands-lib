import Langlands.Representation.Hecke.ActionIntegrand
import Langlands.HarmonicAnalysis.AlgebraicIntegral
import Langlands.Representation.Whittaker.Algebraic

/-! Finite algebraic averaging for coefficients of smooth representations. -/

noncomputable section

namespace Langlands.RankinSelberg.Smearing

open MeasureTheory HarmonicAnalysis Whittaker

universe uX uG uV

variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A compactly supported smooth weighted orbit has a vector integral in the
original algebraic carrier, tested by every algebraic linear functional. -/
theorem exists_weighted_orbit_average (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (U : X → G) (hU : Continuous U) (κ : SchwartzBruhat X) (v : V) :
    ∃ w : V, ∀ L : V →ₗ[ℂ] ℂ,
      Integrable (fun x => κ x * L (ρ (U x) v)) μ ∧
      L w = ∫ x, κ x * L (ρ (U x) v) ∂μ := by
  let a : X → V := fun x => κ x • ρ (U x) v
  have ha : IsLocallyConstant a :=
    κ.locallyConstant.comp₂
      ((Hecke.orbitMap_locallyConstant ρ (hρ v)).comp_continuous hU) (· • ·)
  have hc : HasCompactSupport a := κ.hasCompactSupport.smul_right
  let A := compactlySupportedSimpleFunc a ha hc
  have hA : A.FinMeasSupp μ := compactlySupportedSimpleFunc_finMeasSupp μ a ha hc
  refine ⟨AlgebraicIntegral.integral μ A, ?_⟩
  intro L
  have hLA := hA.map L.map_zero
  have he : (fun x => (A.map L) x) = (fun x => κ x * L (ρ (U x) v)) := by
    funext x
    simp [A, a]
  constructor
  · simpa only [he] using hLA.integrable
  · rw [← AlgebraicIntegral.integral_linearMap A hA L,
      AlgebraicIntegral.integral_eq_bochner _ hLA, he]

/-- The averaged coefficient belongs to the original coefficient image and has
its scalar integral formula at every group element. -/
theorem exists_coefficient_average (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    {N : Subgroup G} {θ : N →* ℂˣ} (ℓ : functionals N θ ρ)
    (U : X → G) (hU : Continuous U) (κ : SchwartzBruhat X)
    (f : (coefficientModel ρ ℓ).toSubmodule) :
    ∃ f₁ : (coefficientModel ρ ℓ).toSubmodule, ∀ h : G,
      Integrable (fun x => κ x * f.val.val (h * U x)) μ ∧
      f₁.val.val h = ∫ x, κ x * f.val.val (h * U x) ∂μ := by
  obtain ⟨v, rfl⟩ := modelMap_surjective ρ ℓ f
  obtain ⟨w, hw⟩ := exists_weighted_orbit_average μ ρ hρ U hU κ v
  refine ⟨modelMap ρ ℓ w, ?_⟩
  intro h
  have hh := hw (ℓ.val.comp (ρ h))
  change Integrable (fun x => κ x * ℓ.val (ρ (h * U x) v)) μ ∧
    ℓ.val (ρ h w) = ∫ x, κ x * ℓ.val (ρ (h * U x) v) ∂μ
  simpa only [LinearMap.comp_apply, map_mul, Module.End.mul_apply] using hh

end Langlands.RankinSelberg.Smearing
