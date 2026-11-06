import Langlands.Geometry.Building.BuildingFacetClosure

/-! # The original rational-point action on facets and closed facets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- Translate the existing facets using the original action on the quotient. -/
def facetTranslateEquiv (g : rationalPoints G) : BuildingFacet B ≃ BuildingFacet B where
  toFun Fc := ⟨g • Fc.val, Fc.property.smul B g⟩
  invFun Fc := ⟨g⁻¹ • Fc.val, Fc.property.smul B g⁻¹⟩
  left_inv Fc := Subtype.ext (inv_smul_smul g Fc.val)
  right_inv Fc := Subtype.ext (smul_inv_smul g Fc.val)

@[simp] theorem facetTranslateEquiv_val (g : rationalPoints G) (Fc : BuildingFacet B) :
    (B.facetTranslateEquiv g Fc).val = g • Fc.val := rfl

@[simp] theorem facetTranslateEquiv_one (Fc : BuildingFacet B) :
    B.facetTranslateEquiv 1 Fc = Fc :=
  Subtype.ext (one_smul _ _)

theorem facetTranslateEquiv_mul (g h : rationalPoints G) (Fc : BuildingFacet B) :
    B.facetTranslateEquiv (g * h) Fc =
      B.facetTranslateEquiv g (B.facetTranslateEquiv h Fc) :=
  Subtype.ext (mul_smul g h Fc.val)

@[simp] theorem facetTranslateEquiv_inv_apply (g : rationalPoints G) (Fc : BuildingFacet B) :
    B.facetTranslateEquiv g⁻¹ (B.facetTranslateEquiv g Fc) = Fc :=
  (B.facetTranslateEquiv g).left_inv Fc

/-- Translating a common chart preserves the original incidence relation. -/
theorem facetPrecedes_translate (g : rationalPoints G)
    {Fc Fd : BuildingFacet B} (hFD : FacetPrecedes B Fc Fd) :
    FacetPrecedes B (B.facetTranslateEquiv g Fc) (B.facetTranslateEquiv g Fd) := by
  obtain ⟨h, Fa, Da, hFa, hFc, hFd⟩ := hFD
  refine ⟨g * h, Fa, Da, hFa, ?_, ?_⟩
  · change (fun x => g • x) '' Fc.val = B.translatedApartmentMap (g * h) '' Fa
    rw [hFc, Set.image_image]
    apply Set.image_congr
    intro a _
    exact (B.translatedApartmentMap_mul g h a).symm
  · change (fun x => g • x) '' Fd.val = B.translatedApartmentMap (g * h) '' Da
    rw [hFd, Set.image_image]
    apply Set.image_congr
    intro a _
    exact (B.translatedApartmentMap_mul g h a).symm

/-- Translation preserves and reflects incidence, without apartment axioms. -/
@[simp] theorem facetPrecedes_translate_iff (g : rationalPoints G)
    (Fc Fd : BuildingFacet B) :
    FacetPrecedes B (B.facetTranslateEquiv g Fc) (B.facetTranslateEquiv g Fd) ↔
      FacetPrecedes B Fc Fd := by
  refine ⟨fun h => ?_, B.facetPrecedes_translate g⟩
  simpa only [facetTranslateEquiv_inv_apply] using B.facetPrecedes_translate g⁻¹ h

/-- Combinatorial closed facets are equivariant for the same action. -/
theorem buildingFacetClosure_translate (g : rationalPoints G) (Fc : BuildingFacet B) :
    B.buildingFacetClosure (B.facetTranslateEquiv g Fc) =
      g • B.buildingFacetClosure Fc := by
  ext x
  constructor
  · rintro ⟨Fd, hDF, hx⟩
    have hDF' : FacetPrecedes B (B.facetTranslateEquiv g⁻¹ Fd) Fc := by
      simpa only [facetTranslateEquiv_inv_apply] using B.facetPrecedes_translate g⁻¹ hDF
    exact ⟨g⁻¹ • x, ⟨B.facetTranslateEquiv g⁻¹ Fd, hDF',
      Set.smul_mem_smul_set hx⟩, smul_inv_smul g x⟩
  · rintro ⟨y, ⟨Fd, hDF, hy⟩, rfl⟩
    exact ⟨B.facetTranslateEquiv g Fd, B.facetPrecedes_translate g hDF,
      Set.smul_mem_smul_set hy⟩

/-- The unique containing facet is equivariant whenever the facet partition holds. -/
theorem buildingFacetAt_eq_translate (hD : B.SatisfiesApartmentAxioms)
    (g : rationalPoints G) (x : B.ReducedBuilding) :
    B.buildingFacetAt (g • x) = B.facetTranslateEquiv g (B.buildingFacetAt x) :=
  (B.buildingFacetAt_eq_iff_mem hD _ _).mpr
    (Set.smul_mem_smul_set (B.mem_buildingFacetAt x))

end Langlands.Geometry.Building.ValuationBuildingData
