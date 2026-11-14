import Langlands.Geometry.Building.AffineFacetDerivativeLocalization

/-! # Prescribed positive rays in original incident affine facets -/

noncomputable section

universe u v

open Filter Topology

namespace Langlands.Geometry.Building.AffineRootSystem

variable {V : Type u} {A : Type v}
  [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)} {x y : A}

private theorem eventually_sign_lineMap_at_zero (ψ : A →ᵃ[ℝ] ℝ) (x y : A)
    (hx : ψ x ≠ 0) :
    ∀ᶠ t : ℝ in 𝓝 0,
      SignType.sign (ψ (AffineMap.lineMap x y t)) = SignType.sign (ψ x) := by
  have hv (t : ℝ) :
      ψ (AffineMap.lineMap x y t) = (1 - t) * ψ x + t * ψ y := by
    simp only [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module]
    ring
  have hc : Continuous (fun t : ℝ => (1 - t) * ψ x + t * ψ y) := by fun_prop
  have ht : Tendsto (fun t : ℝ => (1 - t) * ψ x + t * ψ y)
      (𝓝 0) (𝓝 (ψ x)) := by simpa using hc.tendsto 0
  rcases lt_or_gt_of_ne hx with hx | hx
  · filter_upwards [ht.eventually (gt_mem_nhds hx)] with t ht
    rw [hv, sign_neg ht, sign_neg hx]
  · filter_upwards [ht.eventually (lt_mem_nhds hx)] with t ht
    rw [hv, sign_pos ht, sign_pos hx]

/-- Every sufficiently short positive segment retains the prescribed localized
facet and has original full facet incident above `x`. -/
theorem eventually_lineMap_incident_with_localized_facet
    (hfinite : (segmentRoots Ψ x y).Finite) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      x ∈ facetClosure Ψ (AffineMap.lineMap x y t) ∧
      facet (vanishingRoots Ψ x) (AffineMap.lineMap x y t) =
        facet (vanishingRoots Ψ x) y := by
  let S : Set (A →ᵃ[ℝ] ℝ) :=
    {ψ | ψ ∈ Ψ ∧ ψ x ≠ 0 ∧ ψ x * ψ y ≤ 0}
  have hS : S.Finite := hfinite.subset fun _ h => ⟨h.1, h.2.2⟩
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ∀ ψ ∈ S,
      SignType.sign (ψ (AffineMap.lineMap x y t)) = SignType.sign (ψ x) :=
    hS.eventually_all.mpr fun ψ hψ =>
      eventually_sign_lineMap_at_zero ψ x y hψ.2.1
  have hnearWithin : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ ψ ∈ S,
      SignType.sign (ψ (AffineMap.lineMap x y t)) = SignType.sign (ψ x) :=
    hnear.filter_mono nhdsWithin_le_nhds
  filter_upwards [hnearWithin, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t htS ht
  have hval (ψ : A →ᵃ[ℝ] ℝ) :
      ψ (AffineMap.lineMap x y t) = (1 - t) * ψ x + t * ψ y := by
    simp only [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module]
    ring
  constructor
  · intro ψ hψ
    by_cases hx : ψ x = 0
    · exact Or.inl (sign_eq_zero_iff.mpr hx)
    · right
      by_cases hsep : ψ x * ψ y ≤ 0
      · exact (htS ψ ⟨hψ, hx, hsep⟩).symm
      · have hprod : 0 < ψ x * ψ y := lt_of_not_ge hsep
        rw [hval]
        rcases lt_or_gt_of_ne hx with hx | hx
        · have hy : ψ y < 0 := by nlinarith
          rw [sign_neg hx, sign_neg (by nlinarith [ht.1, ht.2])]
        · have hy : 0 < ψ y := by nlinarith
          rw [sign_pos hx, sign_pos (by nlinarith [ht.1, ht.2])]
  · apply facet_eq_facet_iff.mpr
    intro ψ hψ
    rw [hval, hψ.2, mul_zero, zero_add, sign_mul, sign_pos ht.1, one_mul]

/-- Derivative-facet membership is localized-facet membership after translating
back by the same base point. -/
theorem mem_incidentFacetDerivative_iff (F : IncidentAffineFacet Ψ x) (w : V) :
    w ∈ (incidentFacetDerivative F).val ↔
      w +ᵥ x ∈ (incidentFacetLocalization F).val := by
  rw [incidentFacetDerivative_val]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [vsub_vadd] using hy
  · intro hw
    exact ⟨w +ᵥ x, hw, vadd_vsub w x⟩

/-- A vector in the derivative facet reaches the original full incident facet
along every sufficiently short positive portion of its own ray. Only finite
separation along that ray is required. -/
theorem eventually_pos_smul_vadd_mem_incidentFacet
    (F : IncidentAffineFacet Ψ x) (w : V)
    (hw : w ∈ (incidentFacetDerivative F).val)
    (hfinite : (segmentRoots Ψ x (w +ᵥ x)).Finite) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, (t • w) +ᵥ x ∈ F.val := by
  have hwloc := (mem_incidentFacetDerivative_iff F w).mp hw
  filter_upwards [eventually_lineMap_incident_with_localized_facet hfinite] with t ht
  let z := AffineMap.lineMap x (w +ᵥ x) t
  let H : IncidentAffineFacet Ψ x :=
    ⟨facet Ψ z, isFacet_facet Ψ x, z, rfl,
      facet_subset_facetClosure_iff.mpr ht.1⟩
  have hH : incidentFacetLocalization H = incidentFacetLocalization F := by
    apply Subtype.ext
    rw [incidentFacetLocalization_val_eq H (mem_facet_self Ψ z)]
    exact ht.2.trans (facet_eq_of_mem hwloc)
  have heq : H = F := incidentFacetLocalization_injective hH
  have hz : z ∈ F.val := by
    rw [← heq]
    exact mem_facet_self Ψ z
  simpa only [z, AffineMap.lineMap_apply, vadd_vsub] using hz

/-- A positive scalar less than one on the prescribed derivative ray reaches
the original full facet. -/
theorem exists_pos_smul_vadd_mem_incidentFacet
    (F : IncidentAffineFacet Ψ x) (w : V)
    (hw : w ∈ (incidentFacetDerivative F).val)
    (hfinite : (segmentRoots Ψ x (w +ᵥ x)).Finite) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ (t • w) +ᵥ x ∈ F.val := by
  obtain ⟨t, ht, htI⟩ :=
    ((eventually_pos_smul_vadd_mem_incidentFacet F w hw hfinite).and
      (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
  exact ⟨t, htI.1, htI.2, ht⟩

/-- A chosen positive parameter on the prescribed derivative ray. -/
def incidentFacetRayParameter
    (F : IncidentAffineFacet Ψ x) (w : V)
    (hw : w ∈ (incidentFacetDerivative F).val)
    (hfinite : (segmentRoots Ψ x (w +ᵥ x)).Finite) : ℝ :=
  (exists_pos_smul_vadd_mem_incidentFacet F w hw hfinite).choose

theorem incidentFacetRayParameter_spec
    (F : IncidentAffineFacet Ψ x) (w : V)
    (hw : w ∈ (incidentFacetDerivative F).val)
    (hfinite : (segmentRoots Ψ x (w +ᵥ x)).Finite) :
    0 < incidentFacetRayParameter F w hw hfinite ∧
      incidentFacetRayParameter F w hw hfinite < 1 ∧
      (incidentFacetRayParameter F w hw hfinite • w) +ᵥ x ∈ F.val :=
  (exists_pos_smul_vadd_mem_incidentFacet F w hw hfinite).choose_spec

end Langlands.Geometry.Building.AffineRootSystem
