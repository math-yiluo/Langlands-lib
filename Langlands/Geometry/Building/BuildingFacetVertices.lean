import Langlands.Geometry.Building.AffineTorsorFacetVertices
import Langlands.Geometry.Building.BuildingFacetAction
import Langlands.Geometry.Building.ValuationApartmentMetric

/-! # Finite actual vertices of facets in the valuation quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

local instance : DecidableEq B.ReducedBuilding := Classical.decEq _

/-- Every original building vertex gives a singleton original building facet. -/
theorem IsVertex.isFacet_singleton {x : B.ReducedBuilding} (hx : B.IsVertex x) :
    B.IsFacet {x} := by
  obtain ⟨g, a, rfl, ha⟩ := hx
  exact ⟨g, {a}, ⟨a, ha⟩, by simp only [Set.image_singleton]⟩

/-- The facet partition reflects the original vertex predicate in every
injective original apartment chart. -/
theorem isVertex_translatedApartmentMap_iff
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    (g : rationalPoints G) (a : B.Apartment) :
    B.IsVertex (B.translatedApartmentMap g a) ↔
      AffineRootSystem.IsVertex B.affineRoots a := by
  constructor
  · intro hx
    have hFa : B.IsFacet
        (B.translatedApartmentMap g '' AffineRootSystem.facet B.affineRoots a) :=
      ⟨g, _, AffineRootSystem.isFacet_facet _ _, rfl⟩
    have he := hFa.eq_of_mem_mem B hD (hx.isFacet_singleton B)
      (show B.translatedApartmentMap g a ∈
        B.translatedApartmentMap g '' AffineRootSystem.facet B.affineRoots a from
          ⟨a, AffineRootSystem.mem_facet_self _ _, rfl⟩)
      (Set.mem_singleton _)
    apply (B.translatedApartmentMap_injective hinj g).image_injective
    exact he.trans (Set.image_singleton).symm
  · intro ha
    exact ⟨g, a, rfl, ha⟩

/-- All and only the original quotient vertices in a combinatorial closed facet. -/
def buildingFacetVertices (Fc : BuildingFacet B) : Set B.ReducedBuilding :=
  {x | x ∈ B.buildingFacetClosure Fc ∧ B.IsVertex x}

@[simp] theorem mem_buildingFacetVertices (Fc : BuildingFacet B) (x : B.ReducedBuilding) :
    x ∈ B.buildingFacetVertices Fc ↔
      x ∈ B.buildingFacetClosure Fc ∧ B.IsVertex x := Iff.rfl

/-- The entire actual vertex set has its exact original affine coordinates
in any presentation of the facet. -/
theorem buildingFacetVertices_eq_image
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    (Fc : BuildingFacet B) (g : rationalPoints G) (a : B.Apartment)
    (hFc : Fc.val = B.translatedApartmentMap g '' AffineRootSystem.facet B.affineRoots a) :
    B.buildingFacetVertices Fc = B.translatedApartmentMap g ''
      {q | q ∈ AffineRootSystem.facetClosure B.affineRoots a ∧
        AffineRootSystem.IsVertex B.affineRoots q} := by
  ext x
  change (x ∈ B.buildingFacetClosure Fc ∧ B.IsVertex x) ↔ _
  rw [B.buildingFacetClosure_eq_image hD Fc g a hFc]
  constructor
  · rintro ⟨⟨q, hq, rfl⟩, hv⟩
    exact ⟨q, ⟨hq, (B.isVertex_translatedApartmentMap_iff hD hinj g q).mp hv⟩, rfl⟩
  · rintro ⟨q, ⟨hq, hv⟩, rfl⟩
    exact ⟨⟨q, hq, rfl⟩, (B.isVertex_translatedApartmentMap_iff hD hinj g q).mpr hv⟩

/-- The original rational-point action preserves the entire actual vertex set. -/
theorem buildingFacetVertices_translate (g : rationalPoints G) (Fc : BuildingFacet B) :
    B.buildingFacetVertices (B.facetTranslateEquiv g Fc) =
      g • B.buildingFacetVertices Fc := by
  ext x
  change (x ∈ B.buildingFacetClosure (B.facetTranslateEquiv g Fc) ∧ B.IsVertex x) ↔ _
  rw [B.buildingFacetClosure_translate]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hv⟩
    refine ⟨y, ⟨hy, ?_⟩, rfl⟩
    simpa only [inv_smul_smul] using hv.smul B g⁻¹
  · rintro ⟨y, ⟨hy, hv⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, hv.smul B g⟩

attribute [local instance] metricRootFintype

local instance : NormedAddCommGroup (TranslationSpace B.i) :=
  RootTranslationMetric.normedAddCommGroup B.i

local instance : NormedSpace ℝ (TranslationSpace B.i) :=
  RootTranslationMetric.normedSpace B.i

local instance : FiniteDimensional ℝ (TranslationSpace B.i) :=
  RootTranslationMetric.finiteDimensional B.i

/-- Every actual closed building facet has finitely many original vertices. -/
theorem finite_buildingFacetVertices
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    (Fc : BuildingFacet B) : (B.buildingFacetVertices Fc).Finite := by
  obtain ⟨g, _, ⟨a, rfl⟩, hFc⟩ := Fc.property
  rw [B.buildingFacetVertices_eq_image hD hinj Fc g a hFc]
  have he :
      {q | q ∈ AffineRootSystem.facetClosure B.affineRoots a ∧
        AffineRootSystem.IsVertex B.affineRoots q} =
      (AffineRootSystem.torsorFacetClosureVertexFinset
        hD.isAffineRootSystem_affineRoots a : Set B.Apartment) := by
    ext q
    exact (AffineRootSystem.mem_torsorFacetClosureVertexFinset _ _ _).symm
  rw [he]
  exact (AffineRootSystem.torsorFacetClosureVertexFinset
    hD.isAffineRootSystem_affineRoots a).finite_toSet.image _

/-- The actual vertex set of each closed facet is nonempty, including rank zero. -/
theorem buildingFacetVertices_nonempty
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    (Fc : BuildingFacet B) : (B.buildingFacetVertices Fc).Nonempty := by
  obtain ⟨g, _, ⟨a, rfl⟩, hFc⟩ := Fc.property
  obtain ⟨q, hq⟩ := AffineRootSystem.torsorFacetClosureVertexFinset_nonempty
    hD.isAffineRootSystem_affineRoots a
  rw [B.buildingFacetVertices_eq_image hD hinj Fc g a hFc]
  exact ⟨B.translatedApartmentMap g q, q,
    (AffineRootSystem.mem_torsorFacetClosureVertexFinset _ _ _).mp hq, rfl⟩

/-- A finite encoding by exactly the existing vertices of the existing quotient. -/
def buildingFacetVertexFinset
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    (Fc : BuildingFacet B) : Finset B.ReducedBuilding :=
  (B.finite_buildingFacetVertices hD hinj Fc).toFinset

@[simp] theorem mem_buildingFacetVertexFinset
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    (Fc : BuildingFacet B) (x : B.ReducedBuilding) :
    x ∈ B.buildingFacetVertexFinset hD hinj Fc ↔
      x ∈ B.buildingFacetClosure Fc ∧ B.IsVertex x := by
  simp only [buildingFacetVertexFinset, Set.Finite.mem_toFinset, mem_buildingFacetVertices]

@[simp] theorem coe_buildingFacetVertexFinset
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    (Fc : BuildingFacet B) :
    (B.buildingFacetVertexFinset hD hinj Fc : Set B.ReducedBuilding) =
      B.buildingFacetVertices Fc := by
  ext x
  exact B.mem_buildingFacetVertexFinset hD hinj Fc x

theorem buildingFacetVertexFinset_nonempty
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    (Fc : BuildingFacet B) : (B.buildingFacetVertexFinset hD hinj Fc).Nonempty := by
  obtain ⟨x, hx⟩ := B.buildingFacetVertices_nonempty hD hinj Fc
  exact ⟨x, (B.mem_buildingFacetVertexFinset hD hinj Fc x).mpr hx⟩

/-- In original chart coordinates the quotient finset is the image of the
full torsor vertex finset. -/
theorem buildingFacetVertexFinset_eq_image
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    (Fc : BuildingFacet B) (g : rationalPoints G) (a : B.Apartment)
    (hFc : Fc.val = B.translatedApartmentMap g '' AffineRootSystem.facet B.affineRoots a) :
    B.buildingFacetVertexFinset hD hinj Fc =
      (AffineRootSystem.torsorFacetClosureVertexFinset
        hD.isAffineRootSystem_affineRoots a).image (B.translatedApartmentMap g) := by
  classical
  apply Finset.coe_injective
  rw [B.coe_buildingFacetVertexFinset, Finset.coe_image,
    B.buildingFacetVertices_eq_image hD hinj Fc g a hFc]
  congr 1
  ext q
  exact (AffineRootSystem.mem_torsorFacetClosureVertexFinset _ _ _).symm

/-- The finite encoding respects the original rational-point action. -/
theorem buildingFacetVertexFinset_translate
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    (g : rationalPoints G) (Fc : BuildingFacet B) :
    B.buildingFacetVertexFinset hD hinj (B.facetTranslateEquiv g Fc) =
      (B.buildingFacetVertexFinset hD hinj Fc).image (g • ·) := by
  classical
  apply Finset.coe_injective
  rw [B.coe_buildingFacetVertexFinset, Finset.coe_image,
    B.coe_buildingFacetVertexFinset, B.buildingFacetVertices_translate]
  rfl

/-- Incidence always implies containment of the finite actual vertex sets. -/
theorem buildingFacetVertexFinset_mono
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    {Fc Cc : BuildingFacet B} (hFC : FacetPrecedes B Fc Cc) :
    B.buildingFacetVertexFinset hD hinj Fc ⊆ B.buildingFacetVertexFinset hD hinj Cc := by
  intro x hx
  rw [B.mem_buildingFacetVertexFinset] at hx ⊢
  exact ⟨B.buildingFacetClosure_mono hD hinj hFC hx.1, hx.2⟩

/-- Vertex containment reflects incidence for two facets presented in one
original apartment chart. -/
theorem facetPrecedes_iff_vertexFinset_subset_in_chart
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    (Fc Cc : BuildingFacet B) (g : rationalPoints G) (a b : B.Apartment)
    (hFc : Fc.val = B.translatedApartmentMap g '' AffineRootSystem.facet B.affineRoots a)
    (hCc : Cc.val = B.translatedApartmentMap g '' AffineRootSystem.facet B.affineRoots b) :
    FacetPrecedes B Fc Cc ↔
      B.buildingFacetVertexFinset hD hinj Fc ⊆
        B.buildingFacetVertexFinset hD hinj Cc := by
  classical
  rw [B.facetPrecedes_iff_isFaceOf hD hinj g hFc hCc,
    B.buildingFacetVertexFinset_eq_image hD hinj Fc g a hFc,
    B.buildingFacetVertexFinset_eq_image hD hinj Cc g b hCc,
    Finset.image_subset_image_iff (B.translatedApartmentMap_injective hinj g)]
  exact AffineRootSystem.isFaceOf_facet_iff_torsorVertexFinset_subset
    hD.isAffineRootSystem_affineRoots a b

/-- Every facet contained in a prescribed original apartment has a facet
presentation in that same chart. -/
theorem exists_facet_presentation_in_apartment
    (hD : B.SatisfiesApartmentAxioms) (Fc : BuildingFacet B)
    (g : rationalPoints G) (hFc : Fc.val ⊆ g • B.apartmentImage) :
    ∃ a : B.Apartment,
      Fc.val = B.translatedApartmentMap g '' AffineRootSystem.facet B.affineRoots a := by
  obtain ⟨x, hx⟩ := Fc.property.nonempty
  obtain ⟨a, ha⟩ := (B.range_translatedApartmentMap g).ge (hFc hx)
  have hAt : B.buildingFacetAt (B.translatedApartmentMap g a) = Fc :=
    (B.buildingFacetAt_eq_iff_mem hD _ Fc).mpr (ha ▸ hx)
  exact ⟨a, (congrArg Subtype.val hAt).symm.trans
    (B.buildingFacetAt_translatedApartmentMap hD g a)⟩

/-- In any fixed common original apartment, incidence is precisely finite
actual vertex containment. -/
theorem facetPrecedes_iff_vertexFinset_subset_of_common_apartment
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    (Fc Cc : BuildingFacet B) (g : rationalPoints G)
    (hFc : Fc.val ⊆ g • B.apartmentImage) (hCc : Cc.val ⊆ g • B.apartmentImage) :
    FacetPrecedes B Fc Cc ↔
      B.buildingFacetVertexFinset hD hinj Fc ⊆
        B.buildingFacetVertexFinset hD hinj Cc := by
  obtain ⟨a, ha⟩ := B.exists_facet_presentation_in_apartment hD Fc g hFc
  obtain ⟨b, hb⟩ := B.exists_facet_presentation_in_apartment hD Cc g hCc
  exact B.facetPrecedes_iff_vertexFinset_subset_in_chart hD hinj Fc Cc g a b ha hb

/-- The lower interval of every actual building facet is finite. All its
members lie in one original apartment, so no global common-apartment axiom
or supplied building realization is required. -/
theorem finite_buildingFacets_below
    (hD : B.SatisfiesApartmentAxioms) (hinj : Function.Injective B.apartmentMap)
    (Fc : BuildingFacet B) : {Fd : BuildingFacet B | FacetPrecedes B Fd Fc}.Finite := by
  obtain ⟨g, Fa, _, hFc⟩ := Fc.property
  have hFcsub : Fc.val ⊆ g • B.apartmentImage :=
    hFc ▸ B.translatedApartmentMap_image_subset g Fa
  apply Set.Finite.of_injOn (f := B.buildingFacetVertexFinset hD hinj)
    (t := ↑(B.buildingFacetVertexFinset hD hinj Fc).powerset) ?_ ?_
    (B.buildingFacetVertexFinset hD hinj Fc).powerset.finite_toSet
  · intro Fd hFd
    exact Finset.mem_powerset.mpr (B.buildingFacetVertexFinset_mono hD hinj hFd)
  · intro Fd hFd Fe hFe heq
    have hdsub := B.subset_apartment_of_facetPrecedes hD hFd g hFcsub
    have hesum := B.subset_apartment_of_facetPrecedes hD hFe g hFcsub
    apply B.facetPrecedes_antisymm hD hinj
    · exact (B.facetPrecedes_iff_vertexFinset_subset_of_common_apartment
        hD hinj Fd Fe g hdsub hesum).mpr heq.subset
    · exact (B.facetPrecedes_iff_vertexFinset_subset_of_common_apartment
        hD hinj Fe Fd g hesum hdsub).mpr heq.symm.subset

end Langlands.Geometry.Building.ValuationBuildingData
