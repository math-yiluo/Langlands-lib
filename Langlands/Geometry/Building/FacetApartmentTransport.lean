import Langlands.Geometry.Building.ApartmentFixedPointReduction
import Langlands.Geometry.Building.ChamberParahoricConstancy
import Langlands.Geometry.Building.ValuationApartmentMetric

/-! # Apartment transport fixing an entire common facet -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- The actual sharp fixer fixes the image of its defining subset pointwise. -/
theorem sharpFixer_smul_apartmentMap {Fa : Set B.Apartment}
    {g : rationalPoints G} (hg : g ∈ B.sharpFixer Fa)
    {x : B.Apartment} (hx : x ∈ Fa) :
    g • B.apartmentMap x = B.apartmentMap x :=
  B.mem_fixer.mp (B.sharpFixer_le_fixer x
    (B.apartment.sharpFixer_anti (Set.singleton_subset_iff.mpr hx) hg))

/-- An apartment containing one point of an apartment facet can be transported
to the base apartment by an element fixing the whole facet pointwise. -/
theorem exists_sharpFixer_facet_smul_apartmentImage
    (hD : B.SatisfiesApartmentAxioms)
    {Fa : Set B.Apartment} (hFa : AffineRootSystem.IsFacet B.affineRoots Fa)
    {x : B.Apartment} (hx : x ∈ Fa)
    {Y : Set B.ReducedBuilding} (hY : B.IsApartment Y)
    (hxY : B.apartmentMap x ∈ Y) :
    ∃ g : rationalPoints G, g ∈ B.sharpFixer Fa ∧
      g • Y = B.apartmentImage ∧
      ∀ y ∈ Fa, g • B.apartmentMap y = B.apartmentMap y := by
  obtain ⟨g, hg, hgY⟩ := B.exists_sharpFixer_smul_apartmentImage x hY hxY
  have hgFa : g ∈ B.sharpFixer Fa := by
    change g ∈ B.apartment.sharpFixer Fa
    rwa [B.apartment.sharpFixer_eq_singleton_of_isFacet
      hD.mem_or_two_smul_mem hFa hx]
  exact ⟨g, hgFa, hgY, fun _ hy => B.sharpFixer_smul_apartmentMap hgFa hy⟩

/-- A normalizer element supplies a single affine coordinate change on all
points of a facet shared with a translated apartment. -/
theorem exists_normalizer_eq_on_facet
    (hD : B.SatisfiesApartmentAxioms)
    (hN : B.HasNormalizerApartmentStabilizer)
    (hinj : Function.Injective B.apartmentMap)
    {Fa : Set B.Apartment} (hFa : AffineRootSystem.IsFacet B.affineRoots Fa)
    {x : B.Apartment} (hx : x ∈ Fa)
    (g : rationalPoints G) (hxg : B.apartmentMap x ∈ g • B.apartmentImage) :
    ∃ n : normalizerPoints B.i, ∀ (a y : B.Apartment), y ∈ Fa →
      g • B.apartmentMap a = B.apartmentMap y → n • a = y := by
  obtain ⟨p, _, hpA, hpfix⟩ :=
    B.exists_sharpFixer_facet_smul_apartmentImage hD hFa hx
      (IsApartment.smul B B.isApartment_apartmentImage g) hxg
  have hpg : p * g ∈ normalizerPoints B.i :=
    (HasNormalizerApartmentStabilizer.smul_apartmentImage_eq_iff B hN (p * g)).mp
      (by rwa [mul_smul])
  refine ⟨⟨p * g, hpg⟩, fun a y hy hay => hinj ?_⟩
  rw [← B.normalizer_smul_apartmentMap]
  change (p * g) • B.apartmentMap a = B.apartmentMap y
  rw [mul_smul, hay, hpfix y hy]

/-- An affine change from the coordinates of `g · A` to those of `A`, agreeing
on their common facet. The choice is supplied by the actual sharp fixer. -/
def facetApartmentTransition
    (hD : B.SatisfiesApartmentAxioms)
    (hN : B.HasNormalizerApartmentStabilizer)
    (hinj : Function.Injective B.apartmentMap)
    {Fa : Set B.Apartment} (hFa : AffineRootSystem.IsFacet B.affineRoots Fa)
    {x : B.Apartment} (hx : x ∈ Fa)
    (g : rationalPoints G) (hxg : B.apartmentMap x ∈ g • B.apartmentImage) :
    B.Apartment ≃ᵃ[ℝ] B.Apartment :=
  B.normalizerAction
    (B.exists_normalizer_eq_on_facet hD hN hinj hFa hx g hxg).choose

theorem facetApartmentTransition_eq
    (hD : B.SatisfiesApartmentAxioms)
    (hN : B.HasNormalizerApartmentStabilizer)
    (hinj : Function.Injective B.apartmentMap)
    {Fa : Set B.Apartment} (hFa : AffineRootSystem.IsFacet B.affineRoots Fa)
    {x : B.Apartment} (hx : x ∈ Fa)
    (g : rationalPoints G) (hxg : B.apartmentMap x ∈ g • B.apartmentImage)
    (a y : B.Apartment) (hy : y ∈ Fa)
    (hay : g • B.apartmentMap a = B.apartmentMap y) :
    B.facetApartmentTransition hD hN hinj hFa hx g hxg a = y :=
  (B.exists_normalizer_eq_on_facet hD hN hinj hFa hx g hxg).choose_spec a y hy hay

local instance : Fintype (relativeRoots B.i) := B.metricRootFintype
local instance : MetricSpace B.Apartment := B.apartmentMetricSpace

/-- The chosen transition is an isometry for the constructed apartment metric. -/
theorem facetApartmentTransition_isometry
    (hD : B.SatisfiesApartmentAxioms)
    (hN : B.HasNormalizerApartmentStabilizer)
    (hinj : Function.Injective B.apartmentMap)
    {Fa : Set B.Apartment} (hFa : AffineRootSystem.IsFacet B.affineRoots Fa)
    {x : B.Apartment} (hx : x ∈ Fa)
    (g : rationalPoints G) (hxg : B.apartmentMap x ∈ g • B.apartmentImage) :
    Isometry (B.facetApartmentTransition hD hN hinj hFa hx g hxg) :=
  B.apartment_normalizer_isometry _

/-- Apartment distances agree for a pair of points lying in one common facet.
This lemma makes no assertion about points in two distinct facets. -/
theorem apartment_dist_eq_of_mem_facet
    (hD : B.SatisfiesApartmentAxioms)
    (hN : B.HasNormalizerApartmentStabilizer)
    (hinj : Function.Injective B.apartmentMap)
    {Fa : Set B.Apartment} (hFa : AffineRootSystem.IsFacet B.affineRoots Fa)
    {x y : B.Apartment} (hx : x ∈ Fa) (hy : y ∈ Fa)
    (g : rationalPoints G) (a b : B.Apartment)
    (ha : g • B.apartmentMap a = B.apartmentMap x)
    (hb : g • B.apartmentMap b = B.apartmentMap y) :
    dist a b = dist x y := by
  have hxg : B.apartmentMap x ∈ g • B.apartmentImage :=
    ha ▸ Set.smul_mem_smul_set (show B.apartmentMap a ∈ B.apartmentImage from ⟨a, rfl⟩)
  have heq := (B.facetApartmentTransition_isometry hD hN hinj hFa hx g hxg).dist_eq a b
  rw [B.facetApartmentTransition_eq hD hN hinj hFa hx g hxg a x hx ha,
    B.facetApartmentTransition_eq hD hN hinj hFa hx g hxg b y hy hb] at heq
  exact heq.symm

end Langlands.Geometry.Building.ValuationBuildingData
