import Langlands.Representation.AlgebraicCompactAverage

/-! # Bounded invariant preimages from source averaging -/

noncomputable section
universe uG uV uW
set_option autoImplicit false

namespace Langlands.Representation.AlgebraicCompact

open MeasureTheory
open Langlands.Analysis.FiniteSpanIntegral

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (ρ : _root_.Representation ℂ G V) (hρ : HasFiniteContinuousOrbits ρ)
  (μ : Measure G) [IsFiniteMeasure μ]

/-- Every submodule containing the source orbit contains its average. -/
theorem average_mem_submodule (M : Submodule ℂ V) (v : V)
    (hv : ∀ g : G, ρ g v ∈ M) :
    average ρ hρ μ v ∈ M := by
  apply (Submodule.Quotient.mk_eq_zero M).mp
  apply eq_of_dual_eq
  intro l
  change (l.comp M.mkQ) (average ρ hρ μ v) = l 0
  rw [dual_average]
  have hz (g : G) : M.mkQ (ρ g v) = 0 :=
    (Submodule.Quotient.mk_eq_zero M).mpr (hv g)
  simp only [LinearMap.comp_apply, hz, map_zero, integral_zero]

/-- A linear map with constant image on one orbit preserves that image on averaging.
Only the source orbit is integrated. -/
theorem map_average_eq_of_orbit_constant [IsProbabilityMeasure μ]
    (L : V →ₗ[ℂ] W) (v : V) (hv : ∀ g : G, L (ρ g v) = L v) :
    L (average ρ hρ μ v) = L v := by
  apply eq_of_dual_eq
  intro l
  change (l.comp L) (average ρ hρ μ v) = l (L v)
  rw [dual_average]
  simp only [LinearMap.comp_apply, hv]
  simp

include hρ

/-- Source averaging produces a fixed preimage inside any invariant source bound,
without finite-orbit or topology hypotheses on the target. -/
theorem exists_invariant_preimage_mem [MeasurableMul G] [μ.IsMulLeftInvariant]
    [IsProbabilityMeasure μ]
    (σ : _root_.Representation ℂ G W) (L : V →ₗ[ℂ] W)
    (hL : ∀ (g : G) (v : V), L (ρ g v) = σ g (L v))
    (M : Submodule ℂ V) (hM : ∀ g v, v ∈ M → ρ g v ∈ M)
    (w : W) (hw : w ∈ σ.invariants) (hpre : w ∈ M.map L) :
    ∃ v : V, v ∈ M ∧ v ∈ ρ.invariants ∧ L v = w := by
  obtain ⟨v, hv, rfl⟩ := hpre
  refine ⟨average ρ hρ μ v,
    average_mem_submodule ρ hρ μ M v (fun g => hM g v hv),
    average_mem_invariants ρ hρ μ v, ?_⟩
  exact map_average_eq_of_orbit_constant ρ hρ μ L v (fun g => by
    rw [hL]
    exact hw g)

end Langlands.Representation.AlgebraicCompact
