import Langlands.Geometry.Building.AffineFacetCentroids
import Langlands.Geometry.Building.BuildingFacetVertices

/-! # Canonical centroids of original quotient facets -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

namespace AffineRootSystem

variable {V : Type u} {A : Type v}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

omit [FiniteDimensional ℝ V] in
/-- A root stabilizer transports the full root set to itself. -/
theorem transportedRoots_eq_of_mem_rootStabilizer
    {e : A ≃ᵃ[ℝ] A} (he : e ∈ rootStabilizer Ψ) :
    transportedRoots e Ψ = Ψ := by
  ext ψ
  constructor
  · rintro ⟨phi, hphi, rfl⟩
    exact ((rootStabilizer Ψ).inv_mem he phi).mpr hphi
  · intro hψ
    refine ⟨ψ.comp e.toAffineMap, (comp_mem_iff he ψ).mpr hψ, ?_⟩
    ext x
    change ψ (e (e.symm x)) = ψ x
    rw [e.apply_symm_apply]

/-- The canonical original affine facet centroid commutes with every root
stabilizer, as a consequence of full affine-root transport. -/
theorem facetCentroid_apply_of_mem_rootStabilizer
    (hΨ : IsAffineRootSystemWithRankZero Ψ)
    {e : A ≃ᵃ[ℝ] A} (he : e ∈ rootStabilizer Ψ) (p : A) :
    facetCentroid hΨ (e p) = e (facetCentroid hΨ p) := by
  have h := facetCentroid_transportedRoots hΨ e p
  simpa only [transportedRoots_eq_of_mem_rootStabilizer he] using h

end AffineRootSystem

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

attribute [local instance] metricRootFintype

local instance : NormedAddCommGroup (TranslationSpace B.i) :=
  RootTranslationMetric.normedAddCommGroup B.i

local instance : NormedSpace ℝ (TranslationSpace B.i) :=
  RootTranslationMetric.normedSpace B.i

local instance : FiniteDimensional ℝ (TranslationSpace B.i) :=
  RootTranslationMetric.finiteDimensional B.i

/-- The original normalizer action preserves canonical affine facet centroids. -/
theorem normalizer_smul_facetCentroid (hD : B.SatisfiesApartmentAxioms)
    (n : normalizerPoints B.i) (a : B.Apartment) :
    AffineRootSystem.facetCentroid hD.isAffineRootSystem_affineRoots (n • a) =
      n • AffineRootSystem.facetCentroid hD.isAffineRootSystem_affineRoots a :=
  AffineRootSystem.facetCentroid_apply_of_mem_rootStabilizer
    hD.isAffineRootSystem_affineRoots
    (hD.range_le_extendedAffineWeylGroup ⟨n, rfl⟩).1 a

/-- Equal points of the actual quotient give equal quotient centroids in
any two original translated apartment charts. -/
theorem translated_facetCentroid_eq_of_eq
    (hD : B.SatisfiesApartmentAxioms)
    {g h : rationalPoints G} {a b : B.Apartment}
    (hab : B.translatedApartmentMap g a = B.translatedApartmentMap h b) :
    B.translatedApartmentMap g
        (AffineRootSystem.facetCentroid hD.isAffineRootSystem_affineRoots a) =
      B.translatedApartmentMap h
        (AffineRootSystem.facetCentroid hD.isAffineRootSystem_affineRoots b) := by
  have hab' : (h⁻¹ * g) • B.apartmentMap a = B.apartmentMap b := by
    change g • B.apartmentMap a = h • B.apartmentMap b at hab
    rw [mul_smul, hab, inv_smul_smul]
  obtain ⟨n, hn, heq⟩ :=
    B.exists_normalizer_eq_on_translated_facetClosure hD (h⁻¹ * g) hab'
  have hc := AffineRootSystem.facetCentroid_mem_facet
    hD.isAffineRootSystem_affineRoots a
  have he := congrArg (h • ·)
    (heq _ (AffineRootSystem.facet_subset_facetClosure _ _ hc))
  change g • B.apartmentMap _ = h • B.apartmentMap _
  have hc' : AffineRootSystem.facetCentroid hD.isAffineRootSystem_affineRoots b =
      n • AffineRootSystem.facetCentroid hD.isAffineRootSystem_affineRoots a := by
    rw [← hn, B.normalizer_smul_facetCentroid hD]
  rw [hc']
  simpa only [mul_smul, smul_inv_smul] using he

/-- Every original quotient facet admits an original affine point presentation. -/
theorem exists_facet_point_presentation (Fc : BuildingFacet B) :
    ∃ ga : rationalPoints G × B.Apartment,
      Fc.val = B.translatedApartmentMap ga.1 ''
        AffineRootSystem.facet B.affineRoots ga.2 := by
  obtain ⟨g, _, ⟨a, rfl⟩, hFc⟩ := Fc.property
  exact ⟨(g, a), hFc⟩

/-- The canonical centroid in the actual quotient, initially chosen in one
original chart. Its chart independence is proved below. -/
def buildingFacetCentroid (hD : B.SatisfiesApartmentAxioms) (Fc : BuildingFacet B) :
    B.ReducedBuilding :=
  let ga := (B.exists_facet_point_presentation Fc).choose
  B.translatedApartmentMap ga.1
    (AffineRootSystem.facetCentroid hD.isAffineRootSystem_affineRoots ga.2)

/-- Any original chart presentation computes the same canonical quotient
centroid; no injectivity of apartment charts is needed. -/
theorem buildingFacetCentroid_eq_of_presentation
    (hD : B.SatisfiesApartmentAxioms)
    (Fc : BuildingFacet B) (g : rationalPoints G) (a : B.Apartment)
    (hFc : Fc.val = B.translatedApartmentMap g '' AffineRootSystem.facet B.affineRoots a) :
    B.buildingFacetCentroid hD Fc = B.translatedApartmentMap g
      (AffineRootSystem.facetCentroid hD.isAffineRootSystem_affineRoots a) := by
  let ha := (B.exists_facet_point_presentation Fc).choose
  have hha := (B.exists_facet_point_presentation Fc).choose_spec
  change Fc.val = B.translatedApartmentMap ha.1 ''
    AffineRootSystem.facet B.affineRoots ha.2 at hha
  have hx : B.translatedApartmentMap ha.1 ha.2 ∈ Fc.val :=
    hha ▸ Set.mem_image_of_mem _ (AffineRootSystem.mem_facet_self _ _)
  rw [hFc] at hx
  obtain ⟨b, hb, hbe⟩ := hx
  change B.translatedApartmentMap ha.1
      (AffineRootSystem.facetCentroid hD.isAffineRootSystem_affineRoots ha.2) = _
  rw [B.translated_facetCentroid_eq_of_eq hD hbe.symm]
  rw [AffineRootSystem.facetCentroid_eq_of_facetRel hD.isAffineRootSystem_affineRoots
    ((AffineRootSystem.facetRel_equivalence B.affineRoots).symm hb)]

/-- The canonical quotient centroid lies in its original open facet. -/
theorem buildingFacetCentroid_mem
    (hD : B.SatisfiesApartmentAxioms) (Fc : BuildingFacet B) :
    B.buildingFacetCentroid hD Fc ∈ Fc.val := by
  obtain ⟨⟨g, a⟩, hFc⟩ := B.exists_facet_point_presentation Fc
  rw [B.buildingFacetCentroid_eq_of_presentation hD Fc g a hFc, hFc]
  exact Set.mem_image_of_mem _
    (AffineRootSystem.facetCentroid_mem_facet hD.isAffineRootSystem_affineRoots a)

/-- Taking the containing facet of the centroid recovers the original facet. -/
@[simp] theorem buildingFacetAt_centroid
    (hD : B.SatisfiesApartmentAxioms) (Fc : BuildingFacet B) :
    B.buildingFacetAt (B.buildingFacetCentroid hD Fc) = Fc :=
  (B.buildingFacetAt_eq_iff_mem hD _ _).mpr (B.buildingFacetCentroid_mem hD Fc)

/-- Original quotient facets have distinct canonical centroids. -/
theorem buildingFacetCentroid_injective (hD : B.SatisfiesApartmentAxioms) :
    Function.Injective (B.buildingFacetCentroid hD) := by
  intro Fc Fd he
  have h := congrArg B.buildingFacetAt he
  simpa only [B.buildingFacetAt_centroid hD] using h

/-- The canonical centroid construction respects the original rational-point action. -/
theorem buildingFacetCentroid_translate
    (hD : B.SatisfiesApartmentAxioms) (g : rationalPoints G) (Fc : BuildingFacet B) :
    B.buildingFacetCentroid hD (B.facetTranslateEquiv g Fc) =
      g • B.buildingFacetCentroid hD Fc := by
  obtain ⟨⟨h, a⟩, hFc⟩ := B.exists_facet_point_presentation Fc
  have ht : (B.facetTranslateEquiv g Fc).val =
      B.translatedApartmentMap (g * h) '' AffineRootSystem.facet B.affineRoots a := by
    change (fun x => g • x) '' Fc.val = _
    rw [hFc, Set.image_image]
    apply Set.image_congr
    intro b _
    exact (B.translatedApartmentMap_mul g h b).symm
  rw [B.buildingFacetCentroid_eq_of_presentation hD _ (g * h) a ht,
    B.buildingFacetCentroid_eq_of_presentation hD Fc h a hFc]
  exact B.translatedApartmentMap_mul g h _

end ValuationBuildingData
end Langlands.Geometry.Building
