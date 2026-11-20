import Langlands.Representation.Archimedean.CompactWeightedOrbit
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Squaring a compact average within its weight translation type -/

noncomputable section

open MeasureTheory
open scoped Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (K : Subgroup G) [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ν : Measure K) [IsFiniteMeasure ν]
  {d : ℕ} (τ : K →* Matrix (Fin d) (Fin d) ℂ)
  (F : (Fin d → ℂ) →ₗ[ℂ] C(K, ℂ))

/-- The vector obtained by the weighted compact average within the finite matrix type. -/
def compactWeightedTypeVector (u : Fin d → ℂ) : Fin d → ℂ :=
  ∫ k, F u k • (τ k *ᵥ u) ∂ν

variable [ν.IsMulLeftInvariant]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (R : G →* (E →L[ℂ] E)) (hR : IsContinuousRepresentation R)

local notation "j" => (ContinuousMap.mk Subtype.val continuous_subtype_val : C(K, G))
local notation "P" => compactWeightedOrbit ν R hR j

/-- Squaring an average with weight `F u` gives the same weight family at the
averaged matrix vector. This new weight depends only on the compact data. -/
theorem compactWeightedOrbit_comp_self (hτ : Continuous τ)
    (hF : ∀ (k x : K) (u : Fin d → ℂ), F (τ k *ᵥ u) x = F u (k⁻¹ * x))
    (u : Fin d → ℂ) :
    (P (F u)).comp (P (F u)) = P (F (compactWeightedTypeVector K ν τ F u)) := by
  apply ContinuousLinearMap.ext
  intro v
  let T := compactWeightedIntertwiner K ν R hR τ F hF v
  let L := T.val.toContinuousLinearMap
  have ht (z : Fin d → ℂ) : L z = P (F z) v := rfl
  have hI : Integrable (fun k : K => F u k • (τ k *ᵥ u)) ν :=
    ((F u).continuous.smul (hτ.matrix_mulVec continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change P (F u) (P (F u) v) = P (F (compactWeightedTypeVector K ν τ F u)) v
  rw [← ht u, ← ht (compactWeightedTypeVector K ν τ F u), compactWeightedOrbit_apply]
  change (∫ k : K, F u k • R (k : G) (L u) ∂ν) = L (∫ k, F u k • (τ k *ᵥ u) ∂ν)
  rw [← L.integral_comp_comm hI]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  change F u k • R (k : G) (L u) = L (F u k • (τ k *ᵥ u))
  rw [map_smul]
  congr 1
  exact (T.property k u).symm

end Langlands.Archimedean
