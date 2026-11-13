import Langlands.Geometry.Building.GenericApartmentInjection
import Langlands.Geometry.Building.IntegerBuildingFacetClosure

/-! # Facet order and closure embedding in the integer-valued building -/

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

/-- The original integer-valued apartment embeds in its original quotient.
Connected reductivity and maximal splitness are already part of the data. -/
theorem apartmentMap_injective : Function.Injective B.apartmentMap :=
  B.apartment.apartmentMap_injective B.isConnectedReductive B.isMaximalSplitTorus

/-- In any prescribed common chart, original building incidence is exactly
the original affine face relation, with no extra injectivity premise. -/
theorem facetPrecedes_iff_isFaceOf_in_chart
    {F C : B.BuildingFacet} (g : rationalPoints G) {Fa Ca : Set B.Apartment}
    (hF : F.val = B.translatedApartmentMap g '' Fa)
    (hC : C.val = B.translatedApartmentMap g '' Ca) :
    B.FacetPrecedes F C ↔ AffineRootSystem.IsFaceOf B.affineRoots Fa Ca :=
  B.facetPrecedes_iff_isFaceOf B.apartmentMap_injective g hF hC

/-- Transitivity of the original common-apartment incidence relation. -/
theorem facetPrecedes_trans
    {F C D : B.BuildingFacet}
    (hFC : B.FacetPrecedes F C) (hCD : B.FacetPrecedes C D) :
    B.FacetPrecedes F D := by
  obtain ⟨g, Da, _, hDchart⟩ := D.property
  have hDsub : D.val ⊆ g • B.apartmentImage := by
    rw [hDchart]
    exact B.translatedApartmentMap_image_subset g Da
  obtain ⟨Ca, Da', hCDa, hC, hD'⟩ :=
    B.exists_apartment_faces_of_facetPrecedes hCD g hDsub
  have hCsub : C.val ⊆ g • B.apartmentImage := by
    rw [hC]
    exact B.translatedApartmentMap_image_subset g Ca
  obtain ⟨Fa, Ca', hFCa, hF, hC'⟩ :=
    B.exists_apartment_faces_of_facetPrecedes hFC g hCsub
  have hCa : Ca' = Ca :=
    (B.translatedApartmentMap_injective B.apartmentMap_injective g).image_injective
      (hC'.symm.trans hC)
  rw [hCa] at hFCa
  exact ⟨g, Fa, Da', hFCa.trans hCDa, hF, hD'⟩

/-- Mutual incidence identifies the original full facets. -/
theorem facetPrecedes_antisymm
    {F C : B.BuildingFacet}
    (hFC : B.FacetPrecedes F C) (hCF : B.FacetPrecedes C F) : F = C := by
  obtain ⟨g, Ca, _, hCchart⟩ := C.property
  have hCsub : C.val ⊆ g • B.apartmentImage := by
    rw [hCchart]
    exact B.translatedApartmentMap_image_subset g Ca
  obtain ⟨Fa, Ca', hFCa, hF, hC⟩ :=
    B.exists_apartment_faces_of_facetPrecedes hFC g hCsub
  have hCFa := (B.facetPrecedes_iff_isFaceOf_in_chart g hC hF).mp hCF
  apply Subtype.ext
  exact hF.trans ((congrArg (B.translatedApartmentMap g '' ·)
    (hFCa.antisymm hCFa)).trans hC.symm)

/-- An explicit partial order with exactly the existing incidence relation.
It is not installed as a global instance. -/
@[instance_reducible]
def buildingFacetPartialOrder : PartialOrder B.BuildingFacet where
  le := B.FacetPrecedes
  lt := fun F C => B.FacetPrecedes F C ∧ ¬ B.FacetPrecedes C F
  lt_iff_le_not_ge := fun _ _ => Iff.rfl
  le_refl := B.facetPrecedes_refl
  le_trans := fun _ _ _ => B.facetPrecedes_trans
  le_antisymm := fun _ _ => B.facetPrecedes_antisymm

/-- Incidence gives inclusion of combinatorial closed facets. -/
theorem buildingFacetClosure_mono
    {F C : B.BuildingFacet} (hFC : B.FacetPrecedes F C) :
    B.buildingFacetClosure F ⊆ B.buildingFacetClosure C := by
  rintro _ ⟨D, hDF, hx⟩
  exact ⟨D, B.facetPrecedes_trans hDF hFC, hx⟩

/-- Inclusion of combinatorial closed facets reflects exactly the original
common-apartment face relation. -/
theorem facetPrecedes_iff_buildingFacetClosure_subset (F C : B.BuildingFacet) :
    B.FacetPrecedes F C ↔ B.buildingFacetClosure F ⊆ B.buildingFacetClosure C := by
  refine ⟨B.buildingFacetClosure_mono, fun h => ?_⟩
  exact (B.facetPrecedes_iff_subset_buildingFacetClosure F C).mpr
    ((B.subset_buildingFacetClosure F).trans h)

/-- A combinatorial closed facet determines its original full facet. -/
theorem buildingFacetClosure_injective : Function.Injective B.buildingFacetClosure := by
  intro F C hFC
  apply B.facetPrecedes_antisymm
  · exact (B.facetPrecedes_iff_buildingFacetClosure_subset F C).mpr hFC.subset
  · exact (B.facetPrecedes_iff_buildingFacetClosure_subset C F).mpr hFC.symm.subset

/-- Embed existing full facets into subsets of the same reduced quotient by
taking the union of their incident lower facets. -/
def buildingFacetClosureEmbedding : B.BuildingFacet ↪ Set B.ReducedBuilding :=
  ⟨B.buildingFacetClosure, B.buildingFacetClosure_injective⟩

/-- With the explicit incidence order, the same closure map is an order
embedding into subsets ordered by inclusion. -/
def buildingFacetClosureOrderEmbedding :
    @OrderEmbedding B.BuildingFacet (Set B.ReducedBuilding)
      B.buildingFacetPartialOrder.toLE inferInstance where
  toFun := B.buildingFacetClosure
  inj' := B.buildingFacetClosure_injective
  map_rel_iff' := fun {F C} =>
    (B.facetPrecedes_iff_buildingFacetClosure_subset F C).symm

end IntegerValuationBuildingData

/-- Combinatorial closure embeds the original full-facet incidence into
subset inclusion, over every field with supplied integer-valued building data. -/
def IntegerBuildingFacetOrderStatement : Prop :=
  ∀ (k : Type u) [Field k] (v : Valuation k (WithZero (Multiplicative ℤ)))
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G),
    Function.Injective B.buildingFacetClosure ∧
      ∀ F C : B.BuildingFacet,
        B.FacetPrecedes F C ↔ B.buildingFacetClosure F ⊆ B.buildingFacetClosure C

theorem integerBuildingFacetOrder : IntegerBuildingFacetOrderStatement.{u} := by
  intro k _ v G _ B
  exact ⟨B.buildingFacetClosure_injective, B.facetPrecedes_iff_buildingFacetClosure_subset⟩

end Langlands.Geometry.Building
