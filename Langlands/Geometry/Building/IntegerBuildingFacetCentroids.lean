import Langlands.Geometry.Building.BuildingFacetCentroids
import Langlands.Geometry.Building.IntegerBuildingFacetClosure

/-! # Canonical facet centroids for integer-valued building data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building
namespace IntegerValuationBuildingData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  (B : IntegerValuationBuildingData v G)

/-- The actual relative roots are finite over the arbitrary base field. -/
@[instance_reducible]
def centroidRootFintype : Fintype (relativeRoots B.i) := by
  letI := B.isConnectedReductive.smooth
  exact (B.isMaximalSplitTorus.isSplitSubtorus.1.finite_relativeRoots B.i).fintype

attribute [local instance] centroidRootFintype

local instance : NormedAddCommGroup (TranslationSpace B.i) :=
  RootTranslationMetric.normedAddCommGroup B.i

local instance : NormedSpace ℝ (TranslationSpace B.i) :=
  RootTranslationMetric.normedSpace B.i

local instance : FiniteDimensional ℝ (TranslationSpace B.i) :=
  RootTranslationMetric.finiteDimensional B.i

/-- The original normalizer action preserves canonical affine facet centroids. -/
theorem normalizer_smul_facetCentroid (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots)
    (n : normalizerPoints B.i) (a : B.Apartment) :
    AffineRootSystem.facetCentroid hΨ (n • a) =
      n • AffineRootSystem.facetCentroid hΨ a :=
  AffineRootSystem.facetCentroid_apply_of_mem_rootStabilizer
    hΨ
    (B.apartment.normalizerAffineEquiv_mem_rootStabilizer n) a

/-- Equal points of the actual quotient give equal quotient centroids in
any two original translated apartment charts. -/
theorem translated_facetCentroid_eq_of_eq
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots)
    {g h : rationalPoints G} {a b : B.Apartment}
    (hab : B.translatedApartmentMap g a = B.translatedApartmentMap h b) :
    B.translatedApartmentMap g
        (AffineRootSystem.facetCentroid hΨ a) =
      B.translatedApartmentMap h
        (AffineRootSystem.facetCentroid hΨ b) := by
  have hab' : (h⁻¹ * g) • B.apartmentMap a = B.apartmentMap b := by
    change g • B.apartmentMap a = h • B.apartmentMap b at hab
    rw [mul_smul, hab, inv_smul_smul]
  obtain ⟨n, hn, heq⟩ :=
    B.exists_normalizer_eq_on_translated_facetClosure (h⁻¹ * g) hab'
  have hc := AffineRootSystem.facetCentroid_mem_facet
    hΨ a
  have he := congrArg (h • ·)
    (heq _ (AffineRootSystem.facet_subset_facetClosure _ _ hc))
  change g • B.apartmentMap _ = h • B.apartmentMap _
  have hc' : AffineRootSystem.facetCentroid hΨ b =
      n • AffineRootSystem.facetCentroid hΨ a := by
    rw [← hn, B.normalizer_smul_facetCentroid hΨ]
  rw [hc']
  simpa only [mul_smul, smul_inv_smul] using he

/-- Every original quotient facet admits an original affine point presentation. -/
theorem exists_facet_point_presentation (Fc : B.BuildingFacet) :
    ∃ ga : rationalPoints G × B.Apartment,
      Fc.val = B.translatedApartmentMap ga.1 ''
        AffineRootSystem.facet B.affineRoots ga.2 := by
  obtain ⟨g, _, ⟨a, rfl⟩, hFc⟩ := Fc.property
  exact ⟨(g, a), hFc⟩

/-- The canonical centroid in the actual quotient, initially chosen in one
original chart. Its chart independence is proved below. -/
def buildingFacetCentroid (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots) (Fc : B.BuildingFacet) :
    B.ReducedBuilding :=
  let ga := (B.exists_facet_point_presentation Fc).choose
  B.translatedApartmentMap ga.1
    (AffineRootSystem.facetCentroid hΨ ga.2)

/-- Any original chart presentation computes the same canonical quotient
centroid; no injectivity of apartment charts is needed. -/
theorem buildingFacetCentroid_eq_of_presentation
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots)
    (Fc : B.BuildingFacet) (g : rationalPoints G) (a : B.Apartment)
    (hFc : Fc.val = B.translatedApartmentMap g '' AffineRootSystem.facet B.affineRoots a) :
    B.buildingFacetCentroid hΨ Fc = B.translatedApartmentMap g
      (AffineRootSystem.facetCentroid hΨ a) := by
  let ha := (B.exists_facet_point_presentation Fc).choose
  have hha := (B.exists_facet_point_presentation Fc).choose_spec
  change Fc.val = B.translatedApartmentMap ha.1 ''
    AffineRootSystem.facet B.affineRoots ha.2 at hha
  have hx : B.translatedApartmentMap ha.1 ha.2 ∈ Fc.val :=
    hha ▸ Set.mem_image_of_mem _ (AffineRootSystem.mem_facet_self _ _)
  rw [hFc] at hx
  obtain ⟨b, hb, hbe⟩ := hx
  change B.translatedApartmentMap ha.1
      (AffineRootSystem.facetCentroid hΨ ha.2) = _
  rw [B.translated_facetCentroid_eq_of_eq hΨ hbe.symm]
  rw [AffineRootSystem.facetCentroid_eq_of_facetRel hΨ
    ((AffineRootSystem.facetRel_equivalence B.affineRoots).symm hb)]

/-- The canonical quotient centroid lies in its original open facet. -/
theorem buildingFacetCentroid_mem
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots) (Fc : B.BuildingFacet) :
    B.buildingFacetCentroid hΨ Fc ∈ Fc.val := by
  obtain ⟨⟨g, a⟩, hFc⟩ := B.exists_facet_point_presentation Fc
  rw [B.buildingFacetCentroid_eq_of_presentation hΨ Fc g a hFc, hFc]
  exact Set.mem_image_of_mem _
    (AffineRootSystem.facetCentroid_mem_facet hΨ a)

/-- Taking the containing facet of the centroid recovers the original facet. -/
@[simp] theorem buildingFacetAt_centroid
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots) (Fc : B.BuildingFacet) :
    B.buildingFacetAt (B.buildingFacetCentroid hΨ Fc) = Fc :=
  (B.buildingFacetAt_eq_iff_mem _ _).mpr (B.buildingFacetCentroid_mem hΨ Fc)

/-- Original quotient facets have distinct canonical centroids. -/
theorem buildingFacetCentroid_injective (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots) :
    Function.Injective (B.buildingFacetCentroid hΨ) := by
  intro Fc Fd he
  have h := congrArg B.buildingFacetAt he
  simpa only [B.buildingFacetAt_centroid hΨ] using h

/-- Translating an original facet translates its canonical quotient centroid. -/
theorem buildingFacetCentroid_smul
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots)
    (g : rationalPoints G) (F : B.BuildingFacet) :
    B.buildingFacetCentroid hΨ ⟨(g • ·) '' F.val, F.property.smul B g⟩ =
      g • B.buildingFacetCentroid hΨ F := by
  obtain ⟨⟨h, a⟩, hF⟩ := B.exists_facet_point_presentation F
  have ht : (g • ·) '' F.val =
      B.translatedApartmentMap (g * h) '' AffineRootSystem.facet B.affineRoots a := by
    rw [hF, Set.image_image]
    apply Set.image_congr
    intro b _
    exact (mul_smul g h (B.apartmentMap b)).symm
  rw [B.buildingFacetCentroid_eq_of_presentation hΨ _ (g * h) a ht,
    B.buildingFacetCentroid_eq_of_presentation hΨ F h a hF]
  exact mul_smul g h _

/-- Canonical centroids give an injective section of the containing-facet map. -/
def IntegerBuildingFacetCentroidsStatement : Prop :=
  ∀ hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots,
    (∀ F : B.BuildingFacet, B.buildingFacetCentroid hΨ F ∈ F.val) ∧
    Function.LeftInverse B.buildingFacetAt (B.buildingFacetCentroid hΨ) ∧
    Function.Injective (B.buildingFacetCentroid hΨ)

theorem integerBuildingFacetCentroids : B.IntegerBuildingFacetCentroidsStatement := by
  intro hΨ
  exact ⟨B.buildingFacetCentroid_mem hΨ, B.buildingFacetAt_centroid hΨ,
    B.buildingFacetCentroid_injective hΨ⟩

end IntegerValuationBuildingData
end Langlands.Geometry.Building
