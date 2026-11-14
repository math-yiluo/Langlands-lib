import Langlands.Geometry.Building.AffineChamberSeparation
import Langlands.Geometry.Building.AffineFacetVertexIncidence

/-! # Localizing incident affine facets at the roots through a point -/

noncomputable section

universe u v

open Filter Topology

namespace Langlands.Geometry.Building.AffineRootSystem

variable {V : Type u} {A : Type v}
  [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)} {x y z : A}

/-- Above a common face, roots not vanishing on that face already have
fixed signs. Only the roots through the face can distinguish the facets. -/
theorem facetRel_iff_vanishingRoots_of_incident
    (hy : x ∈ facetClosure Ψ y) (hz : x ∈ facetClosure Ψ z) :
    facetRel Ψ y z ↔ facetRel (vanishingRoots Ψ x) y z := by
  refine ⟨fun h ψ hψ => h ψ hψ.1, fun h ψ hψ => ?_⟩
  by_cases hx : ψ x = 0
  · exact h ψ ⟨hψ, hx⟩
  · have hnx : SignType.sign (ψ x) ≠ 0 := by simpa using hx
    exact ((hy ψ hψ).resolve_left hnx).symm.trans
      ((hz ψ hψ).resolve_left hnx)

/-- Restricting to roots through a common face preserves and reflects
the original combinatorial closure relation. -/
theorem mem_facetClosure_iff_vanishingRoots_of_incident
    (hy : x ∈ facetClosure Ψ y) (hz : x ∈ facetClosure Ψ z) :
    y ∈ facetClosure Ψ z ↔ y ∈ facetClosure (vanishingRoots Ψ x) z := by
  refine ⟨fun h ψ hψ => h ψ hψ.1, fun h ψ hψ => ?_⟩
  by_cases hx : ψ x = 0
  · exact h ψ ⟨hψ, hx⟩
  · have hnx : SignType.sign (ψ x) ≠ 0 := by simpa using hx
    exact Or.inr (((hy ψ hψ).resolve_left hnx).symm.trans
      ((hz ψ hψ).resolve_left hnx))

private theorem eventually_sign_lineMap (ψ : A →ᵃ[ℝ] ℝ) (x y : A)
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

/-- A sufficiently short positive segment starting at `x` realizes the
localized signs of any point, in a full facet incident above `x`.
Only finiteness of the roots separating the two endpoints is required. -/
theorem exists_incident_point_with_localized_facet
    (hfinite : (segmentRoots Ψ x y).Finite) :
    ∃ z : A, x ∈ facetClosure Ψ z ∧
      facet (vanishingRoots Ψ x) z = facet (vanishingRoots Ψ x) y := by
  let S : Set (A →ᵃ[ℝ] ℝ) :=
    {ψ | ψ ∈ Ψ ∧ ψ x ≠ 0 ∧ ψ x * ψ y ≤ 0}
  have hS : S.Finite := hfinite.subset fun _ h => ⟨h.1, h.2.2⟩
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ∀ ψ ∈ S,
      SignType.sign (ψ (AffineMap.lineMap x y t)) = SignType.sign (ψ x) :=
    hS.eventually_all.mpr fun ψ hψ => eventually_sign_lineMap ψ x y hψ.2.1
  have hnearWithin : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ ψ ∈ S,
      SignType.sign (ψ (AffineMap.lineMap x y t)) = SignType.sign (ψ x) :=
    hnear.filter_mono nhdsWithin_le_nhds
  obtain ⟨t, htS, ht⟩ :=
    (hnearWithin.and (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
  have hval (ψ : A →ᵃ[ℝ] ℝ) :
      ψ (AffineMap.lineMap x y t) = (1 - t) * ψ x + t * ψ y := by
    simp only [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module]
    ring
  refine ⟨AffineMap.lineMap x y t, ?_, facet_eq_facet_iff.mpr ?_⟩
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
  · intro ψ hψ
    rw [hval, hψ.2, mul_zero, zero_add, sign_mul, sign_pos ht.1, one_mul]

/-- The original full affine facets whose closures contain the facet of `x`. -/
abbrev IncidentAffineFacet (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) :=
  {F : Set A // IsFaceOf Ψ (facet Ψ x) F}

private theorem incident_representative_mem_closure (F : IncidentAffineFacet Ψ x) :
    x ∈ facetClosure Ψ F.property.2.choose :=
  F.property.2.choose_spec.2 (mem_facet_self Ψ x)

/-- The unique facet for the roots through `x` containing an incident full facet. -/
def incidentFacetLocalization (F : IncidentAffineFacet Ψ x) :
    {F : Set A // IsFacet (vanishingRoots Ψ x) F} :=
  ⟨facet (vanishingRoots Ψ x) F.property.2.choose,
    isFacet_facet _ _⟩

/-- The localization can be computed using any point of the original full facet. -/
theorem incidentFacetLocalization_val_eq (F : IncidentAffineFacet Ψ x)
    (hy : y ∈ F.val) :
    (incidentFacetLocalization F).val = facet (vanishingRoots Ψ x) y := by
  apply facet_eq_facet_iff.mpr
  have h : facetRel Ψ F.property.2.choose y := by
    change y ∈ facet Ψ F.property.2.choose
    rw [F.property.2.choose_spec.1]
    exact hy
  exact fun ψ hψ => h ψ hψ.1

/-- Every incident full facet is contained in its localized facet. -/
theorem subset_incidentFacetLocalization (F : IncidentAffineFacet Ψ x) :
    F.val ⊆ (incidentFacetLocalization F).val := by
  intro y hy
  rw [incidentFacetLocalization_val_eq F hy]
  exact mem_facet_self _ _

/-- The localized facet is characterized uniquely by containing the full facet. -/
theorem incidentFacetLocalization_eq_iff_subset (F : IncidentAffineFacet Ψ x)
    (G : {F : Set A // IsFacet (vanishingRoots Ψ x) F}) :
    incidentFacetLocalization F = G ↔ F.val ⊆ G.val := by
  refine ⟨fun h => h ▸ subset_incidentFacetLocalization F, fun h => ?_⟩
  apply Subtype.ext
  obtain ⟨y, hy⟩ := G.property
  have hz : F.property.2.choose ∈ F.val := by
    simpa only [F.property.2.choose_spec.1] using
      mem_facet_self Ψ F.property.2.choose
  have hzy : F.property.2.choose ∈ facet (vanishingRoots Ψ x) y := by
    rw [hy]
    exact h hz
  exact (facet_eq_of_mem hzy).trans hy

theorem incidentFacetLocalization_injective :
    Function.Injective (@incidentFacetLocalization V A _ _ _ Ψ x) := by
  intro F G h
  apply Subtype.ext
  rw [← F.property.2.choose_spec.1, ← G.property.2.choose_spec.1]
  apply facet_eq_facet_iff.mpr
  apply (facetRel_iff_vanishingRoots_of_incident
    (incident_representative_mem_closure F)
    (incident_representative_mem_closure G)).mpr
  exact facet_eq_facet_iff.mp (congrArg Subtype.val h)

/-- Finiteness along each segment is enough to realize every localized facet. -/
theorem incidentFacetLocalization_surjective
    (hfinite : ∀ y : A, (segmentRoots Ψ x y).Finite) :
    Function.Surjective (@incidentFacetLocalization V A _ _ _ Ψ x) := by
  intro G
  obtain ⟨y, hy⟩ := G.property
  obtain ⟨z, hz, hzy⟩ := exists_incident_point_with_localized_facet (hfinite y)
  let F : IncidentAffineFacet Ψ x :=
    ⟨facet Ψ z, isFacet_facet Ψ x, z, rfl, facet_subset_facetClosure_iff.mpr hz⟩
  refine ⟨F, Subtype.ext ?_⟩
  exact (incidentFacetLocalization_val_eq F (mem_facet_self Ψ z)).trans (hzy.trans hy)

/-- Localization preserves and reflects the pre-existing affine face relation. -/
theorem isFaceOf_incidentFacetLocalization_iff (F G : IncidentAffineFacet Ψ x) :
    IsFaceOf (vanishingRoots Ψ x)
      (incidentFacetLocalization F).val (incidentFacetLocalization G).val ↔
      IsFaceOf Ψ F.val G.val := by
  change IsFaceOf (vanishingRoots Ψ x)
    (facet (vanishingRoots Ψ x) F.property.2.choose)
    (facet (vanishingRoots Ψ x) G.property.2.choose) ↔ _
  conv_rhs => rw [← F.property.2.choose_spec.1, ← G.property.2.choose_spec.1]
  rw [isFaceOf_facet_iff_facetClosure_subset, isFaceOf_facet_iff_facetClosure_subset,
    facetClosure_subset_facetClosure_iff, facetClosure_subset_facetClosure_iff]
  exact (mem_facetClosure_iff_vanishingRoots_of_incident
    (incident_representative_mem_closure F)
    (incident_representative_mem_closure G)).symm

/-- Incident full facets correspond to all facets for the roots through `x`,
with their original face orders. No order is defined by transport. -/
def incidentFacetLocalizationOrderIso
    (hfinite : ∀ y : A, (segmentRoots Ψ x y).Finite) :
    @OrderIso (IncidentAffineFacet Ψ x)
      {F : Set A // IsFacet (vanishingRoots Ψ x) F}
      ⟨fun F G => IsFaceOf Ψ F.val G.val⟩
      ⟨fun F G => IsFaceOf (vanishingRoots Ψ x) F.val G.val⟩ :=
  { Equiv.ofBijective incidentFacetLocalization
      ⟨incidentFacetLocalization_injective,
        incidentFacetLocalization_surjective hfinite⟩ with
    map_rel_iff' := fun {F G} => isFaceOf_incidentFacetLocalization_iff F G }

@[simp] theorem incidentFacetLocalizationOrderIso_apply
    (hfinite : ∀ y : A, (segmentRoots Ψ x y).Finite)
    (F : IncidentAffineFacet Ψ x) :
    incidentFacetLocalizationOrderIso hfinite F = incidentFacetLocalization F := rfl

/-- The corrected affine root-system axioms supply the required finite separation,
including the empty rank-zero case. -/
def IsAffineRootSystemWithRankZero.incidentFacetLocalizationOrderIso
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (x : A) :
    @OrderIso (IncidentAffineFacet Ψ x)
      {F : Set A // IsFacet (vanishingRoots Ψ x) F}
      ⟨fun F G => IsFaceOf Ψ F.val G.val⟩
      ⟨fun F G => IsFaceOf (vanishingRoots Ψ x) F.val G.val⟩ :=
  AffineRootSystem.incidentFacetLocalizationOrderIso (hΨ.finite_segment_roots x)

end Langlands.Geometry.Building.AffineRootSystem
