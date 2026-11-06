import Langlands.Geometry.Building.PointParahoricNormalizer
import Langlands.Geometry.Building.ChamberParahoricConstancy
import Langlands.Geometry.Building.ValuationBuildingApartmentCharts

/-! # Apartment embeddings and facet compatibility for the actual quotient -/

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

/-- Sharp normalizer separation makes the original apartment map injective. -/
theorem apartmentMap_injective_of_rankOne
    (hD : B.SatisfiesApartmentAxioms)
    (hrank : RelativeRoot.HasRankOneFactorization B.i) :
    Function.Injective B.apartmentMap :=
  ApartmentQuotient.apartment_injective B.apartment.sharpFixerFamily
    (fun n x hn => B.normalizer_smul_eq_self_of_mem_sharpFixer hD hrank x n hn)

/-- The original normalizer action sends apartment facets to apartment facets. -/
theorem normalizer_smul_isFacet
    (hD : B.SatisfiesApartmentAxioms)
    {Fa : Set B.Apartment} (hFa : AffineRootSystem.IsFacet B.affineRoots Fa)
    (n : normalizerPoints B.i) :
    AffineRootSystem.IsFacet B.affineRoots (n • Fa) := by
  obtain ⟨x, rfl⟩ := hFa
  refine ⟨n • x, ?_⟩
  exact (AffineRootSystem.image_facet
    (hD.range_le_extendedAffineWeylGroup ⟨n, rfl⟩).1 x).symm

/-- At a common point of a translated facet and the base apartment, the
quotient relation gives one normalizer coordinate change on the whole facet. -/
theorem exists_normalizer_eq_on_translated_facet
    (hD : B.SatisfiesApartmentAxioms)
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
  have hp' : g⁻¹ * (n : rationalPoints G) ∈ B.sharpFixer Fa := by
    change g⁻¹ * (n : rationalPoints G) ∈ B.apartment.sharpFixer Fa
    rw [B.apartment.sharpFixer_eq_singleton_of_isFacet hD.mem_or_two_smul_mem hFa ha]
    change g⁻¹ * 1 * (n : rationalPoints G) ∈ B.sharpFixer {a} at hp
    simpa only [mul_one] using hp
  refine ⟨n, hn, fun y hy => ?_⟩
  have hfix : (g⁻¹ * (n : rationalPoints G)) • B.apartmentMap y =
      B.apartmentMap y :=
    B.mem_fixer.mp (B.sharpFixer_le_fixer y
      (B.apartment.sharpFixer_anti (Set.singleton_subset_iff.mpr hy) hp'))
  have heq := congrArg (g • ·) hfix
  rw [mul_smul, smul_inv_smul, B.normalizer_smul_apartmentMap] at heq
  exact heq.symm

/-- Every building facet meeting the base apartment is an apartment facet
image; this part uses facet constancy and the original quotient relation. -/
theorem exists_isFacet_image_of_isFacet
    (hD : B.SatisfiesApartmentAxioms)
    (Y : Set B.ReducedBuilding) (hY : B.IsFacet Y)
    (hYA : (Y ∩ B.apartmentImage).Nonempty) :
    ∃ Fa : Set B.Apartment, AffineRootSystem.IsFacet B.affineRoots Fa ∧
      Y = B.apartmentMap '' Fa := by
  obtain ⟨g, Fa, hFa, rfl⟩ := hY
  obtain ⟨_, ⟨a, ha, rfl⟩, b, hab⟩ := hYA
  obtain ⟨n, _, heq⟩ :=
    B.exists_normalizer_eq_on_translated_facet hD hFa ha g hab.symm
  refine ⟨n • Fa, B.normalizer_smul_isFacet hD hFa n, ?_⟩
  change (fun y => g • B.apartmentMap y) '' Fa =
    B.apartmentMap '' ((fun y => n • y) '' Fa)
  rw [Set.image_image]
  exact Set.image_congr heq

/-- AS 6 for the existing valuation quotient, retaining the apartment axioms
and actual opposite factor pairs as explicit premises. -/
theorem hasCompatibleApartmentFacets_of_rankOne
    (hD : B.SatisfiesApartmentAxioms)
    (hrank : RelativeRoot.HasRankOneFactorization B.i) :
    B.HasCompatibleApartmentFacets where
  injective := B.apartmentMap_injective_of_rankOne hD hrank
  exists_isFacet_of_isFacet := B.exists_isFacet_image_of_isFacet hD

/-- The original translated apartment chart, now with its injectivity witness
derived from the apartment axioms and opposite factor pairs. -/
def translatedApartmentChartOfRankOne
    (hD : B.SatisfiesApartmentAxioms)
    (hrank : RelativeRoot.HasRankOneFactorization B.i)
    (g : rationalPoints G) :
    B.Apartment ≃ (g • B.apartmentImage : Set B.ReducedBuilding) :=
  B.translatedApartmentChart (B.apartmentMap_injective_of_rankOne hD hrank) g

@[simp]
theorem translatedApartmentChartOfRankOne_apply
    (hD : B.SatisfiesApartmentAxioms)
    (hrank : RelativeRoot.HasRankOneFactorization B.i)
    (g : rationalPoints G) (x : B.Apartment) :
    (B.translatedApartmentChartOfRankOne hD hrank g x : B.ReducedBuilding) =
      g • B.apartmentMap x :=
  rfl

end Langlands.Geometry.Building.ValuationBuildingData
