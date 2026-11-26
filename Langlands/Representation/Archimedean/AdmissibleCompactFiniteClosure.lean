import Langlands.Representation.Archimedean.CompactFiniteClosure

/-! # Compact-finite vectors in the closure of an admissible subspace -/

noncomputable section

open MeasureTheory Set
open scoped Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

/-- A compact-invariant subspace of compact-finite vectors with finite compact multiplicities
contains every compact-finite vector in its norm closure. Admissibility is imposed on the
subspace's algebraic compact action. -/
def AdmissibleCompactFiniteClosureStatement : Prop :=
  ∀ {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (R : G →* (E →L[ℂ] E)) (W : Subrepresentation (normCompactRepresentation K R)),
    IsContinuousRepresentation R → IsAdmissibleGKModule W.toRepresentation →
    (∀ w ∈ W.toSubmodule, FiniteVectors.IsFiniteVector (normCompactRepresentation K R) w) →
    ∀ {v : E}, v ∈ W.toSubmodule.topologicalClosure →
      FiniteVectors.IsFiniteVector (normCompactRepresentation K R) v → v ∈ W.toSubmodule

section CompactAverage

variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (K : Subgroup G) [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (R : G →* (E →L[ℂ] E)) (hR : IsContinuousRepresentation R)
  (W : Subrepresentation (normCompactRepresentation K R))

local notation "ρ" => normCompactRepresentation K R
local notation "ι" => (ContinuousMap.mk Subtype.val continuous_subtype_val : C(K, G))

omit [IsTopologicalGroup G] [ν.IsMulLeftInvariant] in
/-- A compact average of an algebraically finite vector lies in its orbit span. -/
private theorem average_mem_orbitSpan (w : C(K, ℂ)) {z : E}
    (hz : FiniteVectors.IsFiniteVector ρ z) :
    compactWeightedOrbit ν R hR ι w z ∈ FiniteVectors.orbitSpan ρ z := by
  let O := FiniteVectors.orbitSpan ρ z
  let : FiniteDimensional ℂ O := hz
  let : IsClosed (O : Set E) := O.closed_of_finiteDimensional
  let f (k : K) := w k • R (k : G) z
  have hf : Integrable f ν := integrable_compactWeightedOrbit ν R hR ι w z
  rw [compactWeightedOrbit_apply]
  apply (Submodule.Quotient.mk_eq_zero O).mp
  change O.mkQL (∫ k : K, f k ∂ν) = 0
  rw [← O.mkQL.integral_comp_comm hf]
  exact integral_eq_zero_of_ae (Filter.Eventually.of_forall fun k =>
    (Submodule.Quotient.mk_eq_zero O).mpr
      (O.smul_mem (w k) (FiniteVectors.action_mem_orbitSpan ρ k z)))

/-- For a weight in a fixed finite translation type, averaging maps the closure into
an evaluation image of a finite-dimensional compact intertwiner space. -/
private theorem average_mem_of_mem_closure
    (hadm : IsAdmissibleGKModule W.toRepresentation)
    (hW : ∀ w ∈ W.toSubmodule, FiniteVectors.IsFiniteVector ρ w)
    {d : ℕ} (τ : K →* Matrix (Fin d) (Fin d) ℂ) (hτ : Continuous τ)
    (F : (Fin d → ℂ) →ₗ[ℂ] C(K, ℂ))
    (hF : ∀ (k x : K) (u : Fin d → ℂ), F (τ k *ᵥ u) x = F u (k⁻¹ * x))
    (u : Fin d → ℂ) {v : E} (hv : v ∈ W.toSubmodule.topologicalClosure) :
    compactWeightedOrbit ν R hR ι (F u) v ∈ W.toSubmodule := by
  let A := gkIntertwiners W.toRepresentation d τ
  let : FiniteDimensional ℂ A := hadm d τ hτ
  let ev : A →ₗ[ℂ] E := W.toSubmodule.subtype.comp ((LinearMap.applyₗ u).comp A.subtype)
  let P := compactWeightedOrbit ν R hR ι (F u)
  have hclosed : IsClosed (P ⁻¹' (ev.range : Set E)) :=
    ev.range.closed_of_finiteDimensional.preimage P.continuous
  have hsubset : (W.toSubmodule : Set E) ⊆ P ⁻¹' (ev.range : Set E) := by
    intro z hz
    let T := compactWeightedIntertwiner K ν R hR τ F hF z
    have hT (x : Fin d → ℂ) : T.val x ∈ W.toSubmodule :=
      FiniteVectors.orbitSpan_le ρ z W hz
        (average_mem_orbitSpan K ν R hR (F x) (hW z hz))
    let T₀ : A := ⟨T.val.codRestrict W.toSubmodule hT, fun k x =>
      Subtype.ext (T.prop k x)⟩
    exact ⟨T₀, rfl⟩
  obtain ⟨t, ht⟩ := closure_minimal hsubset hclosed hv
  have hm : ev t ∈ W.toSubmodule := (t.val u).prop
  exact ht ▸ hm

end CompactAverage

/-- Compact averaging with the coordinates of a finite orbit recovers the original vector
as a sum of averages that belong to the admissible subspace. -/
theorem admissibleCompactFiniteClosure : AdmissibleCompactFiniteClosureStatement := by
  intro G E _ _ _ K _ _ _ ν _ _ _ _ _ R W hR hadm hW v hv hvfin
  let ρ := normCompactRepresentation K R
  let S := FiniteVectors.orbitSubrepresentation ρ v
  let : FiniteDimensional ℂ S.toSubmodule := hvfin
  let u : S.toSubmodule := ⟨v, FiniteVectors.self_mem_orbitSpan ρ v⟩
  let b := Module.finBasis ℂ S.toSubmodule
  have hinv (k : K) : ρ k v ∈ W.toSubmodule.topologicalClosure := by
    have h := mem_closure_image (R (k : G)).continuous.continuousAt hv
    exact closure_mono (by
      rintro _ ⟨z, hz, rfl⟩
      exact W.apply_mem_toSubmodule k hz) h
  have hS : S.toSubmodule ≤ W.toSubmodule.topologicalClosure :=
    Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact hinv k)
  rw [← show (u : E) = v from rfl, ← sum_compactReconstructionWeight K R hR ν S u]
  apply W.toSubmodule.sum_mem
  intro i _
  let τ := Langlands.KFiniteDual.subMatrix S
  let hτ := continuous_normCompact_subMatrix K R hR S
  exact average_mem_of_mem_closure K ν R hR W hadm hW τ hτ
    (compactInverseCoordinateWeight τ hτ i)
    (compactInverseCoordinateWeight_translate τ hτ i) (b.equivFun u) (hS (b i).prop)

end Langlands.Archimedean
