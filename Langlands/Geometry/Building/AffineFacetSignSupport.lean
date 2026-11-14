import Langlands.Geometry.Building.AffineIncidentFacetLocalization

/-! # Nonnegative root support detects the original affine facet order -/

noncomputable section

universe u v

namespace Langlands.Geometry.Building.AffineRootSystem

variable {V : Type u} {A : Type v}
  [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ Φ : Set (A →ᵃ[ℝ] ℝ)} {x y : A}

/-- The roots nonnegative at the given point. -/
def nonnegativeRootsAt (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) : Set (A →ᵃ[ℝ] ℝ) :=
  {ψ | ψ ∈ Ψ ∧ 0 ≤ ψ x}

/-- The roots nonnegative everywhere on the supplied subset. -/
def nonnegativeRoots (Ψ : Set (A →ᵃ[ℝ] ℝ)) (F : Set A) : Set (A →ᵃ[ℝ] ℝ) :=
  {ψ | ψ ∈ Ψ ∧ ∀ x ∈ F, 0 ≤ ψ x}

/-- Nonnegative support is constant on a facet for any larger arrangement. -/
theorem nonnegativeRoots_subset_facet (hsub : Φ ⊆ Ψ) (x : A) :
    nonnegativeRoots Φ (facet Ψ x) = nonnegativeRootsAt Φ x := by
  ext ψ
  refine ⟨fun h => ⟨h.1, h.2 x (mem_facet_self Ψ x)⟩, fun h => ⟨h.1, ?_⟩⟩
  intro y hy
  rw [← sign_nonneg_iff, ← hy ψ (hsub h.1), sign_nonneg_iff]
  exact h.2

@[simp] theorem nonnegativeRoots_facet (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) :
    nonnegativeRoots Ψ (facet Ψ x) = nonnegativeRootsAt Ψ x :=
  nonnegativeRoots_subset_facet (Set.Subset.refl _) x

/-- Passing from a facet to its combinatorial closure leaves its support unchanged. -/
@[simp] theorem nonnegativeRoots_facetClosure (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) :
    nonnegativeRoots Ψ (facetClosure Ψ x) = nonnegativeRootsAt Ψ x := by
  ext ψ
  refine ⟨fun h => ⟨h.1, h.2 x (mem_facetClosure_self Ψ x)⟩, fun h => ⟨h.1, ?_⟩⟩
  intro y hy
  rcases hy ψ h.1 with hy | hy
  · exact (sign_eq_zero_iff.mp hy).ge
  · rw [← sign_nonneg_iff, hy, sign_nonneg_iff]
    exact h.2

/-- For a negation-stable arrangement, the original face condition is reverse
inclusion of the roots nonnegative at the two points. -/
theorem mem_facetClosure_iff_nonnegativeRootsAt_subset
    (hneg : ∀ ψ ∈ Ψ, -ψ ∈ Ψ) :
    x ∈ facetClosure Ψ y ↔ nonnegativeRootsAt Ψ y ⊆ nonnegativeRootsAt Ψ x := by
  constructor
  · intro h ψ hψ
    refine ⟨hψ.1, ?_⟩
    rcases h ψ hψ.1 with hx | hx
    · exact (sign_eq_zero_iff.mp hx).ge
    · rw [← sign_nonneg_iff, hx, sign_nonneg_iff]
      exact hψ.2
  · intro h ψ hψ
    rcases lt_trichotomy (ψ x) 0 with hx | hx | hx
    · right
      have hy : ψ y < 0 := lt_of_not_ge fun hy => by
        have hnonneg : 0 ≤ ψ x := (h ⟨hψ, hy⟩).2
        exact not_lt_of_ge hnonneg hx
      rw [sign_neg hx, sign_neg hy]
    · exact Or.inl (sign_eq_zero_iff.mpr hx)
    · right
      have hy : 0 < ψ y := by
        by_contra hy
        have hny : 0 ≤ (-ψ) y := by simpa using (le_of_not_gt hy)
        have hnx := (h ⟨hneg ψ hψ, hny⟩).2
        have : ψ x ≤ 0 := by simpa using hnx
        exact this.not_gt hx
      rw [sign_pos hx, sign_pos hy]

/-- The nonnegative half-space intersection recovers the original closed facet. -/
theorem facetClosure_eq_nonnegative_intersection
    (hneg : ∀ ψ ∈ Ψ, -ψ ∈ Ψ) (y : A) :
    facetClosure Ψ y = {x | ∀ ψ ∈ nonnegativeRootsAt Ψ y, 0 ≤ ψ x} := by
  ext x
  rw [mem_facetClosure_iff_nonnegativeRootsAt_subset hneg]
  exact ⟨fun h ψ hψ => (h hψ).2,
    fun h ψ hψ => ⟨hψ.1, h ψ hψ⟩⟩

/-- Equality of nonnegative supports detects the original facets. -/
theorem nonnegativeRootsAt_eq_iff
    (hneg : ∀ ψ ∈ Ψ, -ψ ∈ Ψ) :
    nonnegativeRootsAt Ψ x = nonnegativeRootsAt Ψ y ↔ facetRel Ψ x y := by
  rw [← facetClosure_eq_facetClosure_iff, Set.Subset.antisymm_iff,
    Set.Subset.antisymm_iff, facetClosure_subset_facetClosure_iff,
    facetClosure_subset_facetClosure_iff,
    mem_facetClosure_iff_nonnegativeRootsAt_subset hneg,
    mem_facetClosure_iff_nonnegativeRootsAt_subset hneg]
  exact and_comm

/-- Face incidence is reflected by nonnegative supports on all original facets. -/
theorem isFaceOf_iff_nonnegativeRoots_subset
    (hneg : ∀ ψ ∈ Ψ, -ψ ∈ Ψ) {F G : Set A}
    (hF : IsFacet Ψ F) (hG : IsFacet Ψ G) :
    IsFaceOf Ψ F G ↔ nonnegativeRoots Ψ G ⊆ nonnegativeRoots Ψ F := by
  obtain ⟨x, rfl⟩ := hF
  obtain ⟨y, rfl⟩ := hG
  rw [isFaceOf_facet_iff_facetClosure_subset, facetClosure_subset_facetClosure_iff,
    nonnegativeRoots_facet, nonnegativeRoots_facet,
    mem_facetClosure_iff_nonnegativeRootsAt_subset hneg]

/-- Nonnegative support distinguishes all original facets. -/
theorem nonnegativeRoots_eq_iff
    (hneg : ∀ ψ ∈ Ψ, -ψ ∈ Ψ) {F G : Set A}
    (hF : IsFacet Ψ F) (hG : IsFacet Ψ G) :
    nonnegativeRoots Ψ F = nonnegativeRoots Ψ G ↔ F = G := by
  obtain ⟨x, rfl⟩ := hF
  obtain ⟨y, rfl⟩ := hG
  rw [nonnegativeRoots_facet, nonnegativeRoots_facet,
    nonnegativeRootsAt_eq_iff hneg, facet_eq_facet_iff]

/-- The actual affine face order embeds into reverse inclusion of supports. -/
def facetNonnegativeRootsOrderEmbedding (hneg : ∀ ψ ∈ Ψ, -ψ ∈ Ψ) :
    @OrderEmbedding {F : Set A // IsFacet Ψ F}
      (OrderDual (Set (A →ᵃ[ℝ] ℝ)))
      ⟨fun F G => IsFaceOf Ψ F.val G.val⟩ inferInstance where
  toFun F := OrderDual.toDual (nonnegativeRoots Ψ F.val)
  inj' F G h := Subtype.ext ((nonnegativeRoots_eq_iff hneg F.property G.property).mp
    (congrArg OrderDual.ofDual h))
  map_rel_iff' {F G} :=
    (isFaceOf_iff_nonnegativeRoots_subset hneg F.property G.property).symm

@[simp] theorem facetNonnegativeRootsOrderEmbedding_apply
    (hneg : ∀ ψ ∈ Ψ, -ψ ∈ Ψ) (F : {F : Set A // IsFacet Ψ F}) :
    facetNonnegativeRootsOrderEmbedding hneg F =
      OrderDual.toDual (nonnegativeRoots Ψ F.val) := rfl

/-- Localizing an incident full facet does not alter its vanishing-root support. -/
theorem nonnegativeRoots_incidentFacetLocalization (F : IncidentAffineFacet Ψ x) :
    nonnegativeRoots (vanishingRoots Ψ x) (incidentFacetLocalization F).val =
      nonnegativeRoots (vanishingRoots Ψ x) F.val := by
  change nonnegativeRoots (vanishingRoots Ψ x)
    (facet (vanishingRoots Ψ x) F.property.2.choose) = _
  rw [nonnegativeRoots_facet]
  simpa only [F.property.2.choose_spec.1] using
    (nonnegativeRoots_subset_facet (vanishingRoots_subset Ψ x) F.property.2.choose).symm

private theorem vanishingRoots_stable_neg (hneg : ∀ ψ ∈ Ψ, -ψ ∈ Ψ) :
    ∀ ψ ∈ vanishingRoots Ψ x, -ψ ∈ vanishingRoots Ψ x := by
  intro ψ hψ
  refine ⟨hneg ψ hψ.1, ?_⟩
  change -ψ x = 0
  rw [hψ.2, neg_zero]

/-- On facets above a common face, vanishing-root support detects original incidence. -/
theorem isFaceOf_iff_incident_nonnegativeRoots_subset
    (hneg : ∀ ψ ∈ Ψ, -ψ ∈ Ψ) (F G : IncidentAffineFacet Ψ x) :
    IsFaceOf Ψ F.val G.val ↔
      nonnegativeRoots (vanishingRoots Ψ x) G.val ⊆
        nonnegativeRoots (vanishingRoots Ψ x) F.val := by
  rw [← isFaceOf_incidentFacetLocalization_iff F G,
    isFaceOf_iff_nonnegativeRoots_subset (vanishingRoots_stable_neg hneg)
      (incidentFacetLocalization F).property (incidentFacetLocalization G).property,
    nonnegativeRoots_incidentFacetLocalization,
    nonnegativeRoots_incidentFacetLocalization]

/-- Vanishing-root supports embed the original incident face order into
reverse inclusion, without a finiteness hypothesis. -/
def incidentNonnegativeRootsOrderEmbedding (hneg : ∀ ψ ∈ Ψ, -ψ ∈ Ψ) (x : A) :
    @OrderEmbedding (IncidentAffineFacet Ψ x)
      (OrderDual (Set (A →ᵃ[ℝ] ℝ)))
      ⟨fun F G => IsFaceOf Ψ F.val G.val⟩ inferInstance where
  toFun F := OrderDual.toDual (nonnegativeRoots (vanishingRoots Ψ x) F.val)
  inj' F G h := by
    apply incidentFacetLocalization_injective
    apply (facetNonnegativeRootsOrderEmbedding (vanishingRoots_stable_neg hneg)).injective
    change nonnegativeRoots (vanishingRoots Ψ x) (incidentFacetLocalization F).val =
      nonnegativeRoots (vanishingRoots Ψ x) (incidentFacetLocalization G).val
    rw [nonnegativeRoots_incidentFacetLocalization,
      nonnegativeRoots_incidentFacetLocalization]
    exact congrArg OrderDual.ofDual h
  map_rel_iff' {F G} :=
    (isFaceOf_iff_incident_nonnegativeRoots_subset hneg F G).symm

@[simp] theorem incidentNonnegativeRootsOrderEmbedding_apply
    (hneg : ∀ ψ ∈ Ψ, -ψ ∈ Ψ) (x : A) (F : IncidentAffineFacet Ψ x) :
    incidentNonnegativeRootsOrderEmbedding hneg x F =
      OrderDual.toDual (nonnegativeRoots (vanishingRoots Ψ x) F.val) := rfl

/-- The corrected affine root-system axioms include the negation stability
needed for support detection, including rank zero. -/
def IsAffineRootSystemWithRankZero.incidentNonnegativeRootsOrderEmbedding
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (x : A) :
    @OrderEmbedding (IncidentAffineFacet Ψ x)
      (OrderDual (Set (A →ᵃ[ℝ] ℝ)))
      ⟨fun F G => IsFaceOf Ψ F.val G.val⟩ inferInstance :=
  AffineRootSystem.incidentNonnegativeRootsOrderEmbedding (fun _ hψ => hΨ.neg_mem hψ) x

end Langlands.Geometry.Building.AffineRootSystem
