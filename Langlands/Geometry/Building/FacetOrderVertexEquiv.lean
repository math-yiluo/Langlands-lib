import Langlands.Geometry.Building.AbstractBuilding

/-! # Recovering vertex bijections from polysimplicial facet order isomorphisms -/

noncomputable section

universe u v w z u₂ v₂

namespace Langlands.Geometry.Building.AbstractBuilding.PolysimplicialComplex

variable {ι : Type v} [Finite ι] {V : ι → Type u}
  {ι' : Type z} [Finite ι'] {V' : ι' → Type w}
  (K : PolysimplicialComplex ι V) (L : PolysimplicialComplex ι' V')

/-- The minimal facets are exactly the singleton vertices. -/
theorem minimal_facets_iff (C : Set (∀ i, V i)) :
    Minimal (· ∈ K.facets) C ↔ ∃ x, C = {x} := by
  constructor
  · intro hC
    obtain ⟨x, hx⟩ := nonempty_of_mem_facets hC.1
    exact ⟨x, Set.Subset.antisymm
      (hC.2 (K.singleton_mem_facets x) (Set.singleton_subset_iff.mpr hx))
      (Set.singleton_subset_iff.mpr hx)⟩
  · rintro ⟨x, rfl⟩
    refine ⟨K.singleton_mem_facets x, ?_⟩
    intro D hD hDx
    exact ((nonempty_of_mem_facets hD).subset_singleton_iff.mp hDx).symm.subset

/-- Vertices identify with the minimal facets, without choosing a decomposition anew. -/
def vertexMinimalFacetEquiv :
    (∀ i, V i) ≃ {C | Minimal (· ∈ K.facets) C} :=
  Equiv.ofBijective (fun x => ⟨{x}, (K.minimal_facets_iff _).mpr ⟨x, rfl⟩⟩)
    ⟨fun _ _ h => Set.singleton_injective (congrArg Subtype.val h), by
      intro C
      obtain ⟨x, hx⟩ := (K.minimal_facets_iff C.val).mp C.property
      exact ⟨x, Subtype.ext hx.symm⟩⟩

/-- The vertex bijection induced by an isomorphism of the ordered facet sets. -/
def facetOrderVertexEquiv (e : K.facets ≃o L.facets) :
    (∀ i, V i) ≃ (∀ i, V' i) :=
  K.vertexMinimalFacetEquiv.trans
    (e.mapSetOfPredMinimal.toEquiv.trans L.vertexMinimalFacetEquiv.symm)

theorem facetOrderVertexEquiv_singleton (e : K.facets ≃o L.facets)
    (x : ∀ i, V i) :
    (e ⟨{x}, K.singleton_mem_facets x⟩).val = {K.facetOrderVertexEquiv L e x} :=
  (congrArg Subtype.val (L.vertexMinimalFacetEquiv.apply_symm_apply
    (e.mapSetOfPredMinimal (K.vertexMinimalFacetEquiv x)))).symm

theorem facetOrderVertexEquiv_mem_iff (e : K.facets ≃o L.facets)
    (x : ∀ i, V i) (Fc : K.facets) :
    K.facetOrderVertexEquiv L e x ∈ (e Fc).val ↔ x ∈ Fc.val := by
  have H := e.le_iff_le (x := ⟨{x}, K.singleton_mem_facets x⟩) (y := Fc)
  change (e ⟨{x}, K.singleton_mem_facets x⟩).val ⊆ (e Fc).val ↔ {x} ⊆ Fc.val at H
  rw [K.facetOrderVertexEquiv_singleton L e] at H
  simpa only [Set.singleton_subset_iff] using H

/-- The recovered vertex bijection sends every facet to its prescribed image. -/
theorem facetOrderVertexEquiv_image (e : K.facets ≃o L.facets) (Fc : K.facets) :
    K.facetOrderVertexEquiv L e '' Fc.val = (e Fc).val := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (K.facetOrderVertexEquiv_mem_iff L e x Fc).mpr hx
  · intro hy
    obtain ⟨x, rfl⟩ := (K.facetOrderVertexEquiv L e).surjective y
    exact ⟨x, (K.facetOrderVertexEquiv_mem_iff L e x Fc).mp hy, rfl⟩

/-- A vertex bijection inducing the facet isomorphism is uniquely determined. -/
theorem facetOrderVertexEquiv_unique (e : K.facets ≃o L.facets)
    (f : (∀ i, V i) ≃ (∀ i, V' i))
    (hf : ∀ Fc : K.facets, f '' Fc.val = (e Fc).val) :
    f = K.facetOrderVertexEquiv L e := by
  apply Equiv.ext
  intro x
  apply Set.singleton_injective
  calc
    {f x} = f '' ({x} : Set (∀ i, V i)) := Set.image_singleton.symm
    _ = (e ⟨{x}, K.singleton_mem_facets x⟩).val :=
      hf ⟨{x}, K.singleton_mem_facets x⟩
    _ = {K.facetOrderVertexEquiv L e x} := K.facetOrderVertexEquiv_singleton L e x

@[simp] theorem facetOrderVertexEquiv_refl :
    K.facetOrderVertexEquiv K (OrderIso.refl _) = Equiv.refl _ := by
  symm
  apply K.facetOrderVertexEquiv_unique
  intro Fc
  exact Set.image_id _

theorem facetOrderVertexEquiv_trans {κ : Type v₂} [Finite κ] {U : κ → Type u₂}
    (M : PolysimplicialComplex κ U) (e : K.facets ≃o L.facets)
    (f : L.facets ≃o M.facets) :
    (K.facetOrderVertexEquiv L e).trans (L.facetOrderVertexEquiv M f) =
      K.facetOrderVertexEquiv M (e.trans f) := by
  apply K.facetOrderVertexEquiv_unique
  intro Fc
  change (fun x => L.facetOrderVertexEquiv M f (K.facetOrderVertexEquiv L e x)) ''
    Fc.val = (f (e Fc)).val
  rw [← Set.image_image, K.facetOrderVertexEquiv_image L e,
    L.facetOrderVertexEquiv_image M f]

@[simp] theorem facetOrderVertexEquiv_symm (e : K.facets ≃o L.facets) :
    (K.facetOrderVertexEquiv L e).symm = L.facetOrderVertexEquiv K e.symm := by
  apply L.facetOrderVertexEquiv_unique
  intro Fc
  have H := K.facetOrderVertexEquiv_image L e (e.symm Fc)
  rw [e.apply_symm_apply] at H
  rw [← H]
  exact (K.facetOrderVertexEquiv L e).symm_image_image _

end Langlands.Geometry.Building.AbstractBuilding.PolysimplicialComplex
