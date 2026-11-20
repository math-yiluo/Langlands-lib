import Langlands.Representation.Archimedean.CompactOrbitSmoothness
import Langlands.Representation.KFiniteDual

/-! # Genuine smoothness of norm compact-finite vectors -/

noncomputable section

open MeasureTheory
open scoped Matrix Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

section Coordinates

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  {d : ℕ} (τ : K →* Matrix (Fin d) (Fin d) ℂ) (hτ : Continuous τ)

/-- Apply the inverse matrix action, then take a fixed coordinate. This gives
continuous weights that depend linearly on the original vector. -/
def compactInverseCoordinateWeight (i : Fin d) : (Fin d → ℂ) →ₗ[ℂ] C(K, ℂ) where
  toFun u := ⟨fun k => (τ k⁻¹ *ᵥ u) i,
    (continuous_apply i).comp ((hτ.comp continuous_inv).matrix_mulVec continuous_const)⟩
  map_add' u v := by
    ext k
    change (τ k⁻¹ *ᵥ (u + v)) i = (τ k⁻¹ *ᵥ u) i + (τ k⁻¹ *ᵥ v) i
    rw [Matrix.mulVec_add]
    rfl
  map_smul' c u := by
    ext k
    change (τ k⁻¹ *ᵥ (c • u)) i = c • (τ k⁻¹ *ᵥ u) i
    rw [Matrix.mulVec_smul]
    rfl

theorem compactInverseCoordinateWeight_translate (i : Fin d) (k x : K) (u : Fin d → ℂ) :
    compactInverseCoordinateWeight τ hτ i (τ k *ᵥ u) x =
      compactInverseCoordinateWeight τ hτ i u (k⁻¹ * x) := by
  change (τ x⁻¹ *ᵥ (τ k *ᵥ u)) i = (τ (k⁻¹ * x)⁻¹ *ᵥ u) i
  rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_rev, inv_inv]

end Coordinates

section Action

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
  [MeasurableSpace Aˣ] [BorelSpace Aˣ] (μ : Measure Aˣ) [μ.IsHaarMeasure]
  (K : Subgroup Aˣ) [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (R : Aˣ →* (E →L[ℂ] E)) (hR : IsContinuousRepresentation R)

local notation "I" => 𝓘(ℝ, A)
local notation "j" => (ContinuousMap.mk Subtype.val continuous_subtype_val : C(K, Aˣ))

include μ ν hR in
/-- Every norm compact-finite vector in an admissible continuous Banach representation
of the units of a finite-dimensional real Banach algebra is genuinely smooth. -/
theorem isSmoothVector_of_normCompactFinite (hadm : IsAdmissible R K)
    (v : E) (hK : FiniteVectors.IsFiniteVector (normCompactRepresentation K R) v) :
    IsSmoothVector I R v := by
  let ρ := normCompactRepresentation K R
  let M := FiniteVectors.orbitSubrepresentation ρ v
  let : FiniteDimensional ℂ M.toSubmodule := hK
  let d := Module.finrank ℂ M.toSubmodule
  let b := Module.finBasis ℂ M.toSubmodule
  let τ := Langlands.KFiniteDual.subMatrix M
  have hτ : Continuous τ := by
    refine continuous_matrix fun i l => ?_
    have h : Continuous (fun k : K => M.toRepresentation k (b l)) :=
      (hR.comp (continuous_subtype_val.prodMk continuous_const)).subtype_mk _
    exact ((b.coord i).toContinuousLinearMap.continuous.comp h).congr
      (fun k => (Langlands.KFiniteDual.subMatrix_apply M k i l).symm)
  let vM : M.toSubmodule := ⟨v, FiniteVectors.self_mem_orbitSpan ρ v⟩
  let u := b.equivFun vM
  let W := fun i : Fin d => compactInverseCoordinateWeight τ hτ i
  let P := fun i : Fin d => compactWeightedOrbit ν R hR j (W i u)
  have hP (i : Fin d) : FiniteDimensional ℂ (P i).toLinearMap.range :=
    finiteDimensional_range_compactWeightedOrbit K ν R hR τ (W i)
      (compactInverseCoordinateWeight_translate τ hτ i) hadm hτ u
  have hs (i : Fin d) : P i (b i : E) ∈ smoothVectors I R :=
    isSmoothVector_compactWeightedOrbit_of_finiteRange ν R hR j (W i u) μ (hP i) (b i)
  have hsum : (∑ i, P i (b i : E)) = v := by
    simp only [P, compactWeightedOrbit_apply]
    rw [← integral_finsetSum Finset.univ (fun i _ =>
      integrable_compactWeightedOrbit ν R hR j (W i u) (b i : E))]
    calc
      _ = ∫ _ : K, v ∂ν := by
        apply integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        change (∑ i : Fin d, W i u k • R (k : Aˣ) (b i : E)) = v
        have hrep : b.equivFun.symm (τ k⁻¹ *ᵥ u) = M.toRepresentation k⁻¹ vM := by
          have h := Langlands.KFiniteDual.equivFun_symm_coordRep M k⁻¹ u
          rw [Langlands.KFiniteDual.coordRep_apply] at h
          change b.equivFun.symm (τ k⁻¹ *ᵥ u) =
            M.toRepresentation k⁻¹ (b.equivFun.symm u) at h
          rw [h]
          exact congrArg (M.toRepresentation k⁻¹) (b.equivFun.symm_apply_apply vM)
        have hcoord : (∑ i : Fin d, W i u k • (b i : E)) = R ((k⁻¹ : K) : Aˣ) v := by
          calc
            _ = ((b.equivFun.symm (τ k⁻¹ *ᵥ u) : M.toSubmodule) : E) := by
              change (∑ i : Fin d, (τ k⁻¹ *ᵥ u) i • M.toSubmodule.subtype (b i)) =
                M.toSubmodule.subtype (b.equivFun.symm (τ k⁻¹ *ᵥ u))
              have h := congrArg M.toSubmodule.subtype
                (b.equivFun_symm_apply (τ k⁻¹ *ᵥ u)).symm
              simpa only [map_sum, map_smul] using h
            _ = _ := congrArg M.toSubmodule.subtype hrep
        simp_rw [← map_smul]
        rw [← map_sum, hcoord, ← mul_apply_eq_comp, ← map_mul, ← Subgroup.coe_mul,
          mul_inv_cancel, Subgroup.coe_one, map_one, one_apply_eq_self]
      _ = _ := by simp [integral_const, Measure.real]
  rw [← hsum]
  exact (smoothVectors I R).sum_mem (fun i _ => hs i)

end Action

end Langlands.Archimedean
