import Langlands.BruhatTits.RationalPoints.CentralNormKernelCompactnessProof
import Langlands.GroupScheme.Rational.RationalCenterComparisonProof
import Mathlib.Topology.Algebra.Group.Pointwise

/-! # Finite central Cartan covers on the actual rational norm kernel -/

noncomputable section

open scoped Pointwise

namespace Langlands

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The double translates of a set, allowing a final arbitrary central factor. -/
def centralDoubleCover (K : Subgroup G) (T : Set G) : Set G :=
  ((K : Set G) * T * (K : Set G)) * (Subgroup.center G : Set G)

/-- A central coset meets a subgroup in a compact set whenever the subgroup's
intersection with the full center is compact. -/
theorem isCompact_subgroup_central_coset (H : Subgroup G)
    (hHZ : IsCompact ((H ⊓ Subgroup.center G : Subgroup G) : Set G)) (t : G) :
    IsCompact {g : G | g ∈ H ∧ ∃ z ∈ Subgroup.center G, g = t * z} := by
  by_cases he : ∃ g : G, g ∈ H ∧ ∃ z ∈ Subgroup.center G, g = t * z
  · obtain ⟨g, hg, z, hz, rfl⟩ := he
    have hset : {g : G | g ∈ H ∧ ∃ z ∈ Subgroup.center G, g = t * z} =
        (fun c : G => (t * z) * c) ''
          ((H ⊓ Subgroup.center G : Subgroup G) : Set G) := by
      ext x
      constructor
      · rintro ⟨hx, w, hw, rfl⟩
        refine ⟨z⁻¹ * w, ?_, ?_⟩
        · change z⁻¹ * w ∈ H ∧ z⁻¹ * w ∈ Subgroup.center G
          constructor
          · have h := H.mul_mem (H.inv_mem hg) hx
            simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using h
          · exact (Subgroup.center G).mul_mem ((Subgroup.center G).inv_mem hz) hw
        · group
      · rintro ⟨c, hc, rfl⟩
        exact ⟨H.mul_mem hg hc.1, z * c,
          (Subgroup.center G).mul_mem hz hc.2, by group⟩
    rw [hset]
    exact hHZ.image (continuous_const.mul continuous_id)
  · have hset : {g : G | g ∈ H ∧ ∃ z ∈ Subgroup.center G, g = t * z} = ∅ := by
      exact Set.eq_empty_iff_forall_notMem.mpr fun g hg => he ⟨g, hg⟩
    rw [hset]
    exact isCompact_empty

/-- Finite central double translates become compact on a closed subgroup that
contains the compact translating subgroup and meets the center compactly. -/
theorem isCompact_centralDoubleCover_preimage (H K : Subgroup G)
    (hH : IsClosed (H : Set G)) (hK : IsCompact (K : Set G)) (hKH : K ≤ H)
    (hHZ : IsCompact ((H ⊓ Subgroup.center G : Subgroup G) : Set G))
    (T : Set G) (hT : T.Finite) :
    IsCompact ((Subtype.val : H → G) ⁻¹' centralDoubleCover K T) := by
  let E : Set G := ⋃ t ∈ T, {g : G | g ∈ H ∧ ∃ z ∈ Subgroup.center G, g = t * z}
  have hE : IsCompact E :=
    hT.isCompact_biUnion fun t _ => isCompact_subgroup_central_coset H hHZ t
  have hset : ((Subtype.val : H → G) ⁻¹' centralDoubleCover K T) =
      (Subtype.val : H → G) ⁻¹' (((K : Set G) * E) * (K : Set G)) := by
    ext g
    constructor
    · rintro ⟨y, ⟨x, ⟨k₁, hk₁, t, ht, rfl⟩, k₂, hk₂, rfl⟩, z, hz, hg⟩
      have hzcomm := Subgroup.mem_center_iff.mp hz k₂
      have hmove : k₁ * (t * z) * k₂ = (k₁ * t * k₂) * z := by
        simp only [mul_assoc]
        rw [hzcomm]
      have htz : t * z ∈ H := by
        have h := H.mul_mem (H.mul_mem (H.inv_mem (hKH hk₁)) g.property)
          (H.inv_mem (hKH hk₂))
        rw [← hg] at h
        change k₁⁻¹ * ((k₁ * t * k₂) * z) * k₂⁻¹ ∈ H at h
        rw [← hmove] at h
        convert h using 1; group
      refine ⟨k₁ * (t * z), ⟨k₁, hk₁, t * z,
        Set.mem_iUnion₂.mpr ⟨t, ht, htz, z, hz, rfl⟩, rfl⟩, k₂, hk₂, ?_⟩
      calc
        k₁ * (t * z) * k₂ = (k₁ * t * k₂) * z := hmove
        _ = g.val := hg
    · rintro ⟨y, ⟨k₁, hk₁, e, he, rfl⟩, k₂, hk₂, hg⟩
      obtain ⟨t, ht, _, z, hz, rfl⟩ := Set.mem_iUnion₂.mp he
      refine ⟨k₁ * t * k₂, ⟨k₁ * t, ⟨k₁, hk₁, t, ht, rfl⟩, k₂, hk₂, rfl⟩,
        z, hz, ?_⟩
      have hzcomm := Subgroup.mem_center_iff.mp hz k₂
      calc
        (k₁ * t * k₂) * z = k₁ * (t * z) * k₂ := by
          simp only [mul_assoc]
          rw [hzcomm]
        _ = g.val := hg
  rw [hset]
  exact hH.isClosedEmbedding_subtypeVal.isCompact_preimage ((hK.mul hE).mul hK)

end Langlands

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)

/-- The full abstract center, intersected with the actual rational norm kernel,
is compact in the canonical rational-point topology. -/
theorem isCompact_rationalCommonNormKernel_inf_center :
    haveI := hG.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    IsCompact ((rationalCommonNormKernel G ⊓ Subgroup.center (rationalPoints G) :
      Subgroup (rationalPoints G)) : Set (rationalPoints G)) := by
  let := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  rw [inf_comm, ← rationalCenterComparison F G hG]
  exact BruhatTits.RationalPoints.centralNormKernelCompactness F G hG

/-- A finite collection of compact double Cartan charts, with arbitrary full
central factors, has a compact preimage in the actual rational norm kernel. -/
theorem isCompact_rationalNormKernel_centralDoubleCover :
    haveI := hG.isAffineHom
    haveI := hG.smooth
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∀ (K : Subgroup (rationalPoints G)), IsCompact (K : Set (rationalPoints G)) →
      ∀ T : Set (rationalPoints G), T.Finite →
        IsCompact ((Subtype.val : rationalCommonNormKernel G → rationalPoints G) ⁻¹'
          centralDoubleCover K T) := by
  let := hG.isAffineHom
  let := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  intro K hK T hT
  exact isCompact_centralDoubleCover_preimage (rationalCommonNormKernel G) K
    (isClosed_rationalCommonNormKernel G) hK
    (compactSubgroup_le_rationalCommonNormKernel G K hK)
    (isCompact_rationalCommonNormKernel_inf_center G hG) T hT

end Langlands.Plancherel
