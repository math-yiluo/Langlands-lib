import Langlands.Geometry.Building.PointwiseFacetStabilizers
import Langlands.Geometry.Building.CommonApartmentConstruction

/-! # Compatible apartment distances on the existing valuation quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- Under compatible apartment facets, a facet meeting an apartment is wholly
contained in that apartment. -/
theorem IsFacet.subset_apartment_of_mem
    (hA : B.HasCompatibleApartmentFacets)
    {Fc Y : Set B.ReducedBuilding} (hFc : B.IsFacet Fc) (hY : B.IsApartment Y)
    {x : B.ReducedBuilding} (hxF : x ∈ Fc) (hxY : x ∈ Y) : Fc ⊆ Y := by
  obtain ⟨g, rfl⟩ := hY
  have hxA : g⁻¹ • x ∈ B.apartmentImage := by
    simpa only [inv_smul_smul] using Set.smul_mem_smul_set (a := g⁻¹) hxY
  have hxF' : g⁻¹ • x ∈ g⁻¹ • Fc := Set.smul_mem_smul_set hxF
  obtain ⟨Fa, _, hFa⟩ := hA.exists_isFacet_of_isFacet _ (hFc.smul B g⁻¹)
    ⟨g⁻¹ • x, hxF', hxA⟩
  change g⁻¹ • Fc = B.apartmentMap '' Fa at hFa
  have hsub : g⁻¹ • Fc ⊆ B.apartmentImage := by
    rw [hFa]
    rintro _ ⟨a, _, rfl⟩
    exact ⟨a, rfl⟩
  simpa only [smul_inv_smul] using Set.smul_set_mono (a := g) hsub

end ValuationBuildingData

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- Two apartments containing two points admit a transporter fixing both
points, using the facets through those points and their actual fixers. -/
theorem exists_twoPoint_smul_apartment_eq
    (hD : P.SatisfiesApartmentAxioms)
    (hN : P.HasNormalizerApartmentStabilizer)
    (hA : P.HasCompatibleApartmentFacets)
    {Ca : Set P.Apartment} {W : Type u} [Group W]
    {π : P.normalizerInZero →* W} {Sgen : Set W}
    (hT : P.IsBuildingTitsSystem Ca π Sgen)
    {Y Z : Set P.ReducedBuilding} (hY : P.IsApartment Y) (hZ : P.IsApartment Z)
    {x y : P.ReducedBuilding} (hxY : x ∈ Y) (hyY : y ∈ Y)
    (hxZ : x ∈ Z) (hyZ : y ∈ Z) :
    ∃ k : P.zeroSubgroup, (k : rationalPoints G) • Y = Z ∧
      (k : rationalPoints G) • x = x ∧ (k : rationalPoints G) • y = y := by
  obtain ⟨Fc, hxF, hFY⟩ := P.exists_buildingFacet_mem_subset_apartment hY hxY
  obtain ⟨Fd, hyF, hDY⟩ := P.exists_buildingFacet_mem_subset_apartment hY hyY
  have hFZ := Fc.property.subset_apartment_of_mem P.toValuationBuildingData hA hZ hxF hxZ
  have hDZ := Fd.property.subset_apartment_of_mem P.toValuationBuildingData hA hZ hyF hyZ
  obtain ⟨k, hkF, hkD, hkYZ⟩ := hT.exists_twoFacet_smul_apartment_eq hY hZ
    Fc Fd hFY hDY hFZ hDZ
  exact ⟨k, hkYZ, P.facetZeroStabilizer_smul_eq hD hN hA hT Fc k hkF hxF,
    P.facetZeroStabilizer_smul_eq hD hN hA hT Fd k hkD hyF⟩

local instance : Fintype (relativeRoots P.i) := P.toValuationBuildingData.metricRootFintype
local instance : MetricSpace P.Apartment := P.toValuationBuildingData.apartmentMetricSpace

/-- The Euclidean apartment distance is independent of the chart for any pair
of common points, including points in distinct facets. -/
theorem apartment_dist_eq
    (hD : P.SatisfiesApartmentAxioms)
    (hN : P.HasNormalizerApartmentStabilizer)
    (hA : P.HasCompatibleApartmentFacets)
    {Ca : Set P.Apartment} {W : Type u} [Group W]
    {π : P.normalizerInZero →* W} {Sgen : Set W}
    (hT : P.IsBuildingTitsSystem Ca π Sgen)
    (g : rationalPoints G) (a b x y : P.Apartment)
    (ha : g • P.apartmentMap a = P.apartmentMap x)
    (hb : g • P.apartmentMap b = P.apartmentMap y) :
    dist a b = dist x y := by
  have hxg : P.apartmentMap x ∈ g • P.toValuationBuildingData.apartmentImage :=
    ha ▸ Set.smul_mem_smul_set ⟨a, rfl⟩
  have hyg : P.apartmentMap y ∈ g • P.toValuationBuildingData.apartmentImage :=
    hb ▸ Set.smul_mem_smul_set ⟨b, rfl⟩
  obtain ⟨k, hkA, hkx, hky⟩ := P.exists_twoPoint_smul_apartment_eq hD hN hA hT
    (ValuationBuildingData.IsApartment.smul _
      P.toValuationBuildingData.isApartment_apartmentImage g)
    P.toValuationBuildingData.isApartment_apartmentImage hxg hyg ⟨x, rfl⟩ ⟨y, rfl⟩
  have hn : (k : rationalPoints G) * g ∈ normalizerPoints P.i :=
    (ValuationBuildingData.HasNormalizerApartmentStabilizer.smul_apartmentImage_eq_iff
      P.toValuationBuildingData hN _).mp (by simpa only [mul_smul] using hkA)
  let n : normalizerPoints P.i := ⟨(k : rationalPoints G) * g, hn⟩
  have hna : n • a = x := by
    apply hA.injective
    rw [← P.normalizer_smul_apartmentMap]
    change ((k : rationalPoints G) * g) • P.apartmentMap a = _
    rw [mul_smul, ha, hkx]
  have hnb : n • b = y := by
    apply hA.injective
    rw [← P.normalizer_smul_apartmentMap]
    change ((k : rationalPoints G) * g) • P.apartmentMap b = _
    rw [mul_smul, hb, hky]
  have H := (P.toValuationBuildingData.apartment_normalizer_isometry n).dist_eq a b
  rw [hna, hnb] at H
  exact H.symm

end ParahoricBuildingData

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- Coordinates for two actual quotient points in one translated apartment. -/
structure PairApartmentPresentation (x y : B.ReducedBuilding) where
  group : rationalPoints G
  first : B.Apartment
  second : B.Apartment
  map_first : group • B.apartmentMap first = x
  map_second : group • B.apartmentMap second = y

/-- The supplied building axiom produces coordinates for each pair. -/
theorem nonempty_pairApartmentPresentation
    (R : B.PolysimplicialRealization)
    (hR : AbstractBuilding.IsBuilding R.complex R.apartments)
    (x y : B.ReducedBuilding) : Nonempty (B.PairApartmentPresentation x y) := by
  obtain ⟨_, ⟨g, rfl⟩, hx, hy⟩ := R.exists_isApartment_mem_mem hR x y
  obtain ⟨_, ⟨a, rfl⟩, ha⟩ := hx
  obtain ⟨_, ⟨b, rfl⟩, hb⟩ := hy
  exact ⟨⟨g, a, b, ha, hb⟩⟩

/-- Choose a presentation in an actual common apartment. -/
def pairApartmentPresentation
    (R : B.PolysimplicialRealization)
    (hR : AbstractBuilding.IsBuilding R.complex R.apartments)
    (x y : B.ReducedBuilding) : B.PairApartmentPresentation x y :=
  Classical.choice (B.nonempty_pairApartmentPresentation R hR x y)

local instance : Fintype (relativeRoots B.i) := B.metricRootFintype
local instance : MetricSpace B.Apartment := B.apartmentMetricSpace

/-- Distance on the original quotient, computed in a chosen common apartment.
Its independence and metric properties are proved separately. -/
def buildingDist
    (R : B.PolysimplicialRealization)
    (hR : AbstractBuilding.IsBuilding R.complex R.apartments)
    (x y : B.ReducedBuilding) : ℝ :=
  let p := B.pairApartmentPresentation R hR x y
  dist p.first p.second

theorem buildingDist_nonneg
    (R : B.PolysimplicialRealization)
    (hR : AbstractBuilding.IsBuilding R.complex R.apartments)
    (x y : B.ReducedBuilding) : 0 ≤ B.buildingDist R hR x y := dist_nonneg

/-- Zero distance separates points already at the presentation level. -/
theorem eq_of_buildingDist_eq_zero
    (R : B.PolysimplicialRealization)
    (hR : AbstractBuilding.IsBuilding R.complex R.apartments)
    {x y : B.ReducedBuilding} (hxy : B.buildingDist R hR x y = 0) : x = y := by
  let p := B.pairApartmentPresentation R hR x y
  have hab : p.first = p.second := dist_eq_zero.mp hxy
  have H := congrArg (fun a => p.group • B.apartmentMap a) hab
  simpa only [p.map_first, p.map_second] using H

end ValuationBuildingData

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)
  (hD : P.SatisfiesApartmentAxioms)
  (hN : P.HasNormalizerApartmentStabilizer)
  (hA : P.HasCompatibleApartmentFacets)
  {Ca : Set P.Apartment} {W : Type u} [Group W]
  {π : P.normalizerInZero →* W} {Sgen : Set W}
  (hT : P.IsBuildingTitsSystem Ca π Sgen)

local instance : Fintype (relativeRoots P.i) := P.toValuationBuildingData.metricRootFintype
local instance : MetricSpace P.Apartment := P.toValuationBuildingData.apartmentMetricSpace

include hD hN hA hT

/-- All common-apartment presentations compute the same distance. -/
theorem pairApartmentPresentation_dist_eq
    {x y : P.ReducedBuilding}
    (p q : P.toValuationBuildingData.PairApartmentPresentation x y) :
    dist p.first p.second = dist q.first q.second := by
  symm
  apply P.apartment_dist_eq hD hN hA hT (p.group⁻¹ * q.group)
  · simpa only [mul_smul, q.map_first, inv_smul_smul] using
      (congrArg (fun z => p.group⁻¹ • z) p.map_first).symm
  · simpa only [mul_smul, q.map_second, inv_smul_smul] using
      (congrArg (fun z => p.group⁻¹ • z) p.map_second).symm

variable (R : P.toValuationBuildingData.PolysimplicialRealization)
  (hR : AbstractBuilding.IsBuilding R.complex R.apartments)

/-- The chosen distance equals the coordinate distance in every presentation. -/
theorem buildingDist_eq_of_presentation
    {x y : P.ReducedBuilding}
    (p : P.toValuationBuildingData.PairApartmentPresentation x y) :
    P.toValuationBuildingData.buildingDist R hR x y = dist p.first p.second :=
  P.pairApartmentPresentation_dist_eq hD hN hA hT
    (P.toValuationBuildingData.pairApartmentPresentation R hR x y) p

/-- Every translated original apartment preserves the constructed distance. -/
theorem buildingDist_translatedApartmentMap
    (g : rationalPoints G) (a b : P.Apartment) :
    P.toValuationBuildingData.buildingDist R hR
      (g • P.apartmentMap a) (g • P.apartmentMap b) = dist a b :=
  P.buildingDist_eq_of_presentation hD hN hA hT R hR ⟨g, a, b, rfl, rfl⟩

/-- In particular the original base chart preserves the distance. -/
theorem buildingDist_apartmentMap (a b : P.Apartment) :
    P.toValuationBuildingData.buildingDist R hR
      (P.apartmentMap a) (P.apartmentMap b) = dist a b := by
  simpa only [one_smul] using
    P.buildingDist_translatedApartmentMap hD hN hA hT R hR 1 a b

/-- The existing rational-point action preserves the distance. -/
theorem buildingDist_smul (g : rationalPoints G) (x y : P.ReducedBuilding) :
    P.toValuationBuildingData.buildingDist R hR (g • x) (g • y) =
      P.toValuationBuildingData.buildingDist R hR x y := by
  let p := P.toValuationBuildingData.pairApartmentPresentation R hR x y
  rw [P.buildingDist_eq_of_presentation hD hN hA hT R hR p]
  have H := P.buildingDist_translatedApartmentMap hD hN hA hT R hR
    (g * p.group) p.first p.second
  simpa only [mul_smul, p.map_first, p.map_second] using H

/-- Symmetry follows by reversing one common-apartment presentation. -/
theorem buildingDist_comm (x y : P.ReducedBuilding) :
    P.toValuationBuildingData.buildingDist R hR x y =
      P.toValuationBuildingData.buildingDist R hR y x := by
  let p := P.toValuationBuildingData.pairApartmentPresentation R hR x y
  rw [P.buildingDist_eq_of_presentation hD hN hA hT R hR p,
    P.buildingDist_eq_of_presentation hD hN hA hT R hR
      ⟨p.group, p.second, p.first, p.map_second, p.map_first⟩]
  exact dist_comm _ _

/-- The diagonal distance vanishes. -/
theorem buildingDist_self (x : P.ReducedBuilding) :
    P.toValuationBuildingData.buildingDist R hR x x = 0 := by
  obtain ⟨g, a, rfl⟩ := P.toValuationBuildingData.exists_smul_apartmentMap x
  rw [P.buildingDist_translatedApartmentMap hD hN hA hT R hR, dist_self]

end ParahoricBuildingData

end Langlands.Geometry.Building
