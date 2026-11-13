import Langlands.Geometry.Building.IntegerValuationBuildingData
import Langlands.Geometry.Building.BuildingFacetPartition
import Langlands.Geometry.Building.NormalizerAffineRootAction
import Langlands.Geometry.Building.AffineRootDoubling
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof

/-! # Facets partition the actual integer-valued quotient over arbitrary fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  (B : IntegerValuationBuildingData v G)

/-- Reductivity and maximal splitness supply AS4 without any apartment-axiom premise. -/
theorem affineRoot_mem_or_two_smul_mem :
    ∀ ψ ∈ B.apartment.extendedAffineRoots,
      ψ ∈ B.affineRoots ∨ (2 : ℝ) • ψ ∈ B.affineRoots := by
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  have hrank : RelativeRoot.HasRankOneFactorization B.i :=
    rootRankOneFactorization k G B.isConnectedReductive B.S B.i B.isMaximalSplitTorus
  have hpair : RelativeRoot.HasOppositeFactorPairs B.i :=
    fun a ha g hg hg1 => (hrank a ha g hg hg1).1.exists
  intro ψ hψ
  exact B.apartment.mem_or_two_smul_mem_affineRoots_of_oppositePairs
    B.isMaximalSplitTorus.isSplitSubtorus.1 hpair hψ

/-- The original normalizer sends each full apartment facet onto a full facet. -/
theorem normalizer_smul_isFacet {Fa : Set B.Apartment}
    (hFa : AffineRootSystem.IsFacet B.affineRoots Fa) (n : normalizerPoints B.i) :
    AffineRootSystem.IsFacet B.affineRoots (n • Fa) := by
  obtain ⟨x, rfl⟩ := hFa
  refine ⟨n • x, ?_⟩
  exact (AffineRootSystem.image_facet
    (B.apartment.normalizerAffineEquiv_mem_rootStabilizer n) x).symm

/-- A quotient coordinate change at one facet point agrees on its entire facet. -/
theorem exists_normalizer_eq_on_translated_facet
    {Fa : Set B.Apartment} (hFa : AffineRootSystem.IsFacet B.affineRoots Fa)
    {a b : B.Apartment} (ha : a ∈ Fa) (g : rationalPoints G)
    (hab : g • B.apartmentMap a = B.apartmentMap b) :
    ∃ n : normalizerPoints B.i, n • a = b ∧
      ∀ y ∈ Fa, g • B.apartmentMap y = B.apartmentMap (n • y) := by
  have hab' :
      ApartmentQuotient.mk B.apartment.sharpFixerFamily (g, a) =
        ApartmentQuotient.mk B.apartment.sharpFixerFamily (1, b) := by
    have h :
        ApartmentQuotient.mk B.apartment.sharpFixerFamily (g * 1, a) =
          ApartmentQuotient.mk B.apartment.sharpFixerFamily (1, b) := hab
    simpa only [mul_one] using h
  obtain ⟨n, hn, hp⟩ :=
    (ApartmentQuotient.mk_eq_mk_iff B.apartment.sharpFixerFamily g 1 a b).mp hab'
  have hp' : g⁻¹ * (n : rationalPoints G) ∈ B.apartment.sharpFixer Fa := by
    rw [B.apartment.sharpFixer_eq_singleton_of_isFacet
      B.affineRoot_mem_or_two_smul_mem hFa ha]
    change g⁻¹ * 1 * (n : rationalPoints G) ∈ B.apartment.sharpFixer {a} at hp
    simpa only [mul_one] using hp
  refine ⟨n, hn, fun y hy => ?_⟩
  have hfix : (g⁻¹ * (n : rationalPoints G)) • B.apartmentMap y =
      B.apartmentMap y :=
    B.apartment.mem_reducedFixer.mp (B.apartment.sharpFixer_le_reducedFixer y
      (B.apartment.sharpFixer_anti (Set.singleton_subset_iff.mpr hy) hp'))
  have heq := congrArg (g • ·) hfix
  rw [mul_smul, smul_inv_smul, B.normalizer_smul_apartmentMap] at heq
  exact heq.symm

/-- Two building facets that share one point are equal as subsets of this quotient. -/
theorem IsFacet.eq_of_mem_mem
    {Y Z : Set B.ReducedBuilding} (hY : B.IsFacet Y) (hZ : B.IsFacet Z)
    {x : B.ReducedBuilding} (hxY : x ∈ Y) (hxZ : x ∈ Z) : Y = Z := by
  obtain ⟨g, Fa, hFa, rfl⟩ := hY
  obtain ⟨h, Fb, hFb, rfl⟩ := hZ
  obtain ⟨a, ha, rfl⟩ := hxY
  obtain ⟨b, hb, hab⟩ := hxZ
  change h • B.apartmentMap b = g • B.apartmentMap a at hab
  have hab' : (h⁻¹ * g) • B.apartmentMap a = B.apartmentMap b := by
    rw [mul_smul, ← hab, inv_smul_smul]
  obtain ⟨n, hn, heq⟩ := B.exists_normalizer_eq_on_translated_facet hFa ha (h⁻¹ * g) hab'
  have hnFa : n • Fa = Fb :=
    (B.normalizer_smul_isFacet hFa n).eq_of_mem_mem hFb
      (hn ▸ Set.smul_mem_smul_set ha) hb
  calc
    (fun y => g • B.apartmentMap y) '' Fa =
        (fun y => h • B.apartmentMap (n • y)) '' Fa := by
      apply Set.image_congr
      intro y hy
      have H := congrArg (h • ·) (heq y hy)
      simpa only [mul_smul, smul_inv_smul] using H
    _ = (fun y => h • B.apartmentMap y) '' (n • Fa) := by
      change _ = (fun y => h • B.apartmentMap y) '' ((fun y => n • y) '' Fa)
      rw [Set.image_image]
    _ = _ := by rw [hnFa]

/-- Every point of the original quotient lies in a full building facet. -/
theorem exists_isFacet_mem (x : B.ReducedBuilding) :
    ∃ Y : Set B.ReducedBuilding, B.IsFacet Y ∧ x ∈ Y := by
  obtain ⟨g, a, rfl⟩ := B.exists_smul_apartmentMap x
  refine ⟨(fun y => g • B.apartmentMap y) '' AffineRootSystem.facet B.affineRoots a,
    ⟨g, _, AffineRootSystem.isFacet_facet _ _, rfl⟩, ?_⟩
  exact ⟨a, AffineRootSystem.mem_facet_self _ _, rfl⟩

/-- The existing full building facets form a partition without a local-field premise. -/
theorem existsUnique_isFacet_mem (x : B.ReducedBuilding) :
    ∃! Y : Set B.ReducedBuilding, B.IsFacet Y ∧ x ∈ Y := by
  obtain ⟨Y, hY, hx⟩ := B.exists_isFacet_mem x
  exact ⟨Y, ⟨hY, hx⟩, fun Z hZ => hZ.1.eq_of_mem_mem B hY hZ.2 hx⟩

/-- The actual full facets of the integer-valued quotient. -/
abbrev BuildingFacet : Type u :=
  {Y : Set B.ReducedBuilding // B.IsFacet Y}

/-- The unique full facet through a quotient point. -/
def buildingFacetAt (x : B.ReducedBuilding) : B.BuildingFacet :=
  ⟨(B.exists_isFacet_mem x).choose, (B.exists_isFacet_mem x).choose_spec.1⟩

theorem mem_buildingFacetAt (x : B.ReducedBuilding) :
    x ∈ (B.buildingFacetAt x).val :=
  (B.exists_isFacet_mem x).choose_spec.2

/-- Containment characterizes this same chosen facet. -/
theorem buildingFacetAt_eq_iff_mem (x : B.ReducedBuilding) (F : B.BuildingFacet) :
    B.buildingFacetAt x = F ↔ x ∈ F.val := by
  constructor
  · intro h
    rw [← h]
    exact B.mem_buildingFacetAt x
  · intro h
    exact Subtype.ext ((B.buildingFacetAt x).property.eq_of_mem_mem B F.property
      (B.mem_buildingFacetAt x) h)

end IntegerValuationBuildingData

/-- The partition assertion for the published integer-valued building data. -/
def IntegerBuildingFacetPartitionStatement : Prop :=
  ∀ (k : Type u) [Field k] (v : Valuation k (WithZero (Multiplicative ℤ)))
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G) (x : B.ReducedBuilding),
    ∃! Y : Set B.ReducedBuilding, B.IsFacet Y ∧ x ∈ Y

theorem integerBuildingFacetPartition : IntegerBuildingFacetPartitionStatement.{u} := by
  intro k _ v G _ B x
  exact B.existsUnique_isFacet_mem x

end Langlands.Geometry.Building
