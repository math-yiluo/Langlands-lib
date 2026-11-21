import Langlands.Representation.Archimedean.CompactFiniteSmoothness
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-! # Norm closure recovers a compact-invariant submodule on compact-finite vectors -/

noncomputable section

open MeasureTheory Set Filter
open scoped Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace Langlands.Archimedean

variable {G E : Type*} [Group G] [TopologicalSpace G]
  (K : Subgroup G) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (R : G →* (E →L[ℂ] E)) (hR : IsContinuousRepresentation R)

local notation "ρK" => normCompactRepresentation K R
local notation "j" => (ContinuousMap.mk Subtype.val continuous_subtype_val : C(K, G))

section Reconstruction

/-- The norm-continuous action has continuous matrix entries on a finite-dimensional
compact subrepresentation equipped with its inherited norm. -/
theorem continuous_normCompact_subMatrix (hcont : IsContinuousRepresentation R)
    (S : Subrepresentation ρK) [FiniteDimensional ℂ S.toSubmodule] :
    Continuous (fun k : K => Langlands.KFiniteDual.subMatrix S k) := by
  let b := Module.finBasis ℂ S.toSubmodule
  refine continuous_matrix fun i l => ?_
  have h : Continuous (fun k : K => S.toRepresentation k (b l)) :=
    (hcont.comp (continuous_subtype_val.prodMk continuous_const)).subtype_mk _
  exact ((b.coord i).toContinuousLinearMap.continuous.comp h).congr
    (fun k => (Langlands.KFiniteDual.subMatrix_apply S k i l).symm)

variable [IsTopologicalGroup G]

/-- The `i`th inverse-action coordinate of `v` in the chosen basis of a finite-dimensional
compact subrepresentation. These are the weights used to reconstruct `v` by averaging. -/
def compactReconstructionWeight (hcont : IsContinuousRepresentation R)
    (S : Subrepresentation ρK) [FiniteDimensional ℂ S.toSubmodule]
    (i : Fin (Module.finrank ℂ S.toSubmodule)) (v : S.toSubmodule) : C(K, ℂ) :=
  compactInverseCoordinateWeight (Langlands.KFiniteDual.subMatrix S)
    (continuous_normCompact_subMatrix K R hcont S) i
    ((Module.finBasis ℂ S.toSubmodule).equivFun v)

variable [CompactSpace K] [MeasurableSpace K] [BorelSpace K] [CompleteSpace E]
  (ν : Measure K) [IsProbabilityMeasure ν]

/-- Reconstruct a vector from averages of the basis vectors with its inverse-action coordinates. -/
theorem sum_compactReconstructionWeight
    (S : Subrepresentation ρK) [FiniteDimensional ℂ S.toSubmodule] (v : S.toSubmodule) :
    (∑ i : Fin (Module.finrank ℂ S.toSubmodule),
      compactWeightedOrbit ν R hR j (compactReconstructionWeight K R hR S i v)
      ((Module.finBasis ℂ S.toSubmodule) i : E)) = (v : E) := by
  let d := Module.finrank ℂ S.toSubmodule
  let b := Module.finBasis ℂ S.toSubmodule
  let τ := Langlands.KFiniteDual.subMatrix S
  change (∑ i : Fin d, compactWeightedOrbit ν R hR j (compactReconstructionWeight K R hR S i v)
    (b i : E)) = (v : E)
  simp only [compactWeightedOrbit_apply]
  rw [← integral_finsetSum Finset.univ (fun i _ =>
    integrable_compactWeightedOrbit ν R hR j (compactReconstructionWeight K R hR S i v) (b i : E))]
  calc
    _ = ∫ _ : K, (v : E) ∂ν := by
      apply integral_congr_ae (Eventually.of_forall fun k => ?_)
      change (∑ i : Fin d, compactReconstructionWeight K R hR S i v k • R (k : G) (b i : E)) = v.val
      have hrep : b.equivFun.symm (τ k⁻¹ *ᵥ b.equivFun v) = S.toRepresentation k⁻¹ v := by
        have h := Langlands.KFiniteDual.equivFun_symm_coordRep S k⁻¹ (b.equivFun v)
        rw [Langlands.KFiniteDual.coordRep_apply] at h
        change b.equivFun.symm (τ k⁻¹ *ᵥ b.equivFun v) =
          S.toRepresentation k⁻¹ (b.equivFun.symm (b.equivFun v)) at h
        rwa [LinearEquiv.symm_apply_apply] at h
      have hcoord : (∑ i : Fin d, compactReconstructionWeight K R hR S i v k • (b i : E)) =
          R ((k⁻¹ : K) : G) (v : E) := by
        calc
          _ = ((b.equivFun.symm (τ k⁻¹ *ᵥ b.equivFun v) : S.toSubmodule) : E) := by
            change (∑ i : Fin d, (τ k⁻¹ *ᵥ b.equivFun v) i • S.toSubmodule.subtype (b i)) =
              S.toSubmodule.subtype (b.equivFun.symm (τ k⁻¹ *ᵥ b.equivFun v))
            simpa only [map_sum, map_smul] using congrArg S.toSubmodule.subtype
              (b.equivFun_symm_apply (τ k⁻¹ *ᵥ b.equivFun v)).symm
          _ = _ := congrArg S.toSubmodule.subtype hrep
      simp_rw [← map_smul]
      rw [← map_sum, hcoord, ← mul_apply_eq_comp, ← map_mul, ← Subgroup.coe_mul,
        mul_inv_cancel, Subgroup.coe_one, map_one, one_apply_eq_self]
    _ = _ := by simp [integral_const, Measure.real]

end Reconstruction

variable [CompactSpace K] [MeasurableSpace K] [BorelSpace K] [CompleteSpace E]
  (ν : Measure K) [IsProbabilityMeasure ν]

private theorem compactWeightedOrbit_mem_of_finiteVector
    (w : C(K, ℂ)) {v : E} (hv : FiniteVectors.IsFiniteVector ρK v) :
    compactWeightedOrbit ν R hR j w v ∈ FiniteVectors.orbitSpan ρK v := by
  let M := FiniteVectors.orbitSpan ρK v
  let : FiniteDimensional ℂ M := hv
  let : IsClosed (M : Set E) := M.closed_of_finiteDimensional
  let f := fun k : K => w k • R (k : G) v
  have hf : Integrable f ν := integrable_compactWeightedOrbit ν R hR j w v
  have hm (k : K) : f k ∈ M :=
    M.smul_mem _ (FiniteVectors.action_mem_orbitSpan ρK k v)
  rw [compactWeightedOrbit_apply]
  apply (Submodule.Quotient.mk_eq_zero M).1
  change M.mkQL (∫ k, f k ∂ν) = 0
  rw [← M.mkQL.integral_comp_comm hf]
  exact integral_eq_zero_of_ae (Eventually.of_forall fun k => (Submodule.Quotient.mk_eq_zero M).2 (hm k))

private theorem compactWeightedOrbit_mem_of_mem_closure
    (W : Subrepresentation ρK) (hW : ∀ v ∈ W.toSubmodule, FiniteVectors.IsFiniteVector ρK v)
    (w : C(K, ℂ))
    (hfin : FiniteDimensional ℂ (compactWeightedOrbit ν R hR j w).toLinearMap.range)
    {v : E} (hv : v ∈ W.toSubmodule.topologicalClosure) :
    compactWeightedOrbit ν R hR j w v ∈ W.toSubmodule := by
  let P := compactWeightedOrbit ν R hR j w
  let B := W.toSubmodule ⊓ P.toLinearMap.range
  let : FiniteDimensional ℂ P.toLinearMap.range := hfin
  have hclosed : IsClosed (P ⁻¹' (B : Set E)) :=
    (B.closed_of_finiteDimensional).preimage P.continuous
  have hsub : (W.toSubmodule : Set E) ⊆ P ⁻¹' (B : Set E) := by
    intro z hz
    refine ⟨?_, ⟨z, rfl⟩⟩
    apply FiniteVectors.orbitSpan_le ρK z W hz
    exact compactWeightedOrbit_mem_of_finiteVector K R hR ν w (hW z hz)
  exact (closure_minimal hsub hclosed hv).1

variable [IsTopologicalGroup G] [ν.IsMulLeftInvariant]

include ν hR in
/-- The norm closure of a compact-invariant subspace of compact-finite vectors contains no
new compact-finite vectors, assuming compact admissibility of the original action. -/
theorem mem_compactSubrepresentation_of_mem_closure (hadm : IsAdmissible R K)
    (W : Subrepresentation ρK) (hW : ∀ v ∈ W.toSubmodule, FiniteVectors.IsFiniteVector ρK v)
    {v : E} (hv : v ∈ W.toSubmodule.topologicalClosure) (hvK : FiniteVectors.IsFiniteVector ρK v) :
    v ∈ W.toSubmodule := by
  let S := FiniteVectors.orbitSubrepresentation ρK v
  let : FiniteDimensional ℂ S.toSubmodule := hvK
  let u : S.toSubmodule := ⟨v, FiniteVectors.self_mem_orbitSpan ρK v⟩
  let b := Module.finBasis ℂ S.toSubmodule
  have hinv (k : K) : ρK k v ∈ W.toSubmodule.topologicalClosure := by
    have h := mem_closure_image (R (k : G)).continuous.continuousAt hv
    exact closure_mono (by rintro _ ⟨z, hz, rfl⟩; exact W.apply_mem_toSubmodule k hz) h
  have hS : S.toSubmodule ≤ W.toSubmodule.topologicalClosure :=
    Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact hinv k)
  rw [← show (u : E) = v from rfl, ← sum_compactReconstructionWeight K R hR ν S u]
  apply W.toSubmodule.sum_mem
  intro i _
  apply compactWeightedOrbit_mem_of_mem_closure K R hR ν W hW _ _ (hS (b i).property)
  exact finiteDimensional_range_compactWeightedOrbit K ν R hR
    (Langlands.KFiniteDual.subMatrix S)
    (compactInverseCoordinateWeight _ (continuous_normCompact_subMatrix K R hR S) i)
    (compactInverseCoordinateWeight_translate _ (continuous_normCompact_subMatrix K R hR S) i)
    hadm (continuous_normCompact_subMatrix K R hR S) (b.equivFun u)

end Langlands.Archimedean
