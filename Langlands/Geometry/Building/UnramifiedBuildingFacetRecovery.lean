import Langlands.Geometry.Building.GenericVertexApartmentRigidity
import Langlands.Geometry.Building.ChamberParahoricConstancy
import Langlands.Geometry.Building.IntegerValuationSharpCoverImage
import Langlands.Geometry.Building.IntegerValuationCommonApartmentsProof
import Langlands.Geometry.Building.IntegerBuildingFacetOrder
import Langlands.Geometry.Building.UnramifiedSplitBoundedPoints

/-! # Recovering full unramified building facets from their zero fixers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- Common apartments turn the apartment sharp-fixer fixed-locus bound into
a bound on all points of the original reduced quotient. -/
theorem exists_mem_facetClosure_apartmentMap_eq_of_fixed_by_sharpFixer
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hcommon : D.HasCommonApartments) (x : D.Apartment) (y : D.ReducedBuilding)
    (hfix : ∀ g : rationalPoints G, g ∈ D.sharpFixer {x} → g • y = y) :
    ∃ b ∈ AffineRootSystem.facetClosure D.affineRoots x,
      D.apartmentMap b = y := by
  obtain ⟨b, hb⟩ := D.exists_apartmentMap_eq_of_fixed_by_sharpFixer
    x y (hcommon (D.apartmentMap x) y) hfix
  refine ⟨b, D.mem_facetClosure_of_fixed_by_sharpFixer hG hi ?_, hb⟩
  simpa only [hb] using hfix

end KPApartmentData

namespace UnramifiedZeroDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
  [IsAffineHom H.X.hom]
  (E : UnramifiedZeroDatum F H) (B : MaximalUnramified.BuildingData F H)

/-- Containment of actual zero fixers on nonempty subsets of two full building
facets reflects reverse incidence, without a common chart assumption. -/
theorem facetPrecedes_of_buildingZeroFixer_le
    {Fc Cc : B.BuildingFacet} {Ω Ω' : Set B.ReducedBuilding}
    (hne : Ω.Nonempty) (hΩ : Ω ⊆ Fc.val)
    (hne' : Ω'.Nonempty) (hΩ' : Ω' ⊆ Cc.val)
    (hle : E.zeroPoints ⊓ B.pointwiseFixer Ω ≤
      E.zeroPoints ⊓ B.pointwiseFixer Ω') :
    B.FacetPrecedes Cc Fc := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy⟩ := hne'
  obtain ⟨g, Fa, hFa, hF⟩ := Fc.property
  obtain ⟨a, ha, _⟩ := hF ▸ hΩ hx
  have hfix : ∀ t : rationalPoints H, t ∈ B.sharpFixer {a} →
      t • (g⁻¹ • y) = g⁻¹ • y := by
    intro t ht
    have htFa : t ∈ B.sharpFixer Fa := by
      change t ∈ B.apartment.sharpFixer Fa
      rw [B.apartment.sharpFixer_eq_singleton_of_isFacet
        B.affineRoot_mem_or_two_smul_mem hFa ha]
      exact ht
    have htΩ : g * t * g⁻¹ ∈ E.zeroPoints ⊓ B.pointwiseFixer Ω := by
      refine ⟨E.normal_zeroPoints.conj_mem t
        (E.sharpFixer_le_zeroPoints B {a} ht) g, ?_⟩
      apply B.apartment.mem_pointwiseFixer.mpr
      intro z hz
      obtain ⟨b, hb, rfl⟩ := hF ▸ hΩ hz
      have htb := B.apartment.mem_pointwiseFixer.mp
        (B.sharpFixer_le_pointwiseFixer Fa htFa) _ ⟨b, hb, rfl⟩
      simp only [mul_smul, inv_smul_smul, htb]
    have hty := B.apartment.mem_pointwiseFixer.mp (hle htΩ).2 y hy
    have hty' := congrArg (g⁻¹ • ·) hty
    simpa only [mul_smul, inv_smul_smul] using hty'
  obtain ⟨b, hb, hby⟩ :=
    B.apartment.exists_mem_facetClosure_apartmentMap_eq_of_fixed_by_sharpFixer
      B.isConnectedReductive B.isMaximalSplitTorus
      (MaximalUnramified.commonApartments F H B) a (g⁻¹ • y) hfix
  have hFa' : AffineRootSystem.facet B.affineRoots a = Fa :=
    (AffineRootSystem.isFacet_facet _ _).eq_of_mem_mem hFa
      (AffineRootSystem.mem_facet_self _ _) ha
  have hF' : Fc.val =
      B.translatedApartmentMap g '' AffineRootSystem.facet B.affineRoots a := by
    rw [hFa']
    exact hF
  apply (B.facetPrecedes_iff_nonempty_inter_buildingFacetClosure Cc Fc).mpr
  refine ⟨y, hΩ' hy, ?_⟩
  rw [B.buildingFacetClosure_eq_image Fc g a hF']
  refine ⟨b, hb, ?_⟩
  change g • B.apartment.apartmentMap b = y
  rw [hby, smul_inv_smul]

/-- Equality of zero fixers on arbitrary nonempty facet subsets determines
the full building facets. -/
theorem buildingFacet_eq_of_zeroFixer_eq
    {Fc Cc : B.BuildingFacet} {Ω Ω' : Set B.ReducedBuilding}
    (hne : Ω.Nonempty) (hΩ : Ω ⊆ Fc.val)
    (hne' : Ω'.Nonempty) (hΩ' : Ω' ⊆ Cc.val)
    (heq : E.zeroPoints ⊓ B.pointwiseFixer Ω =
      E.zeroPoints ⊓ B.pointwiseFixer Ω') :
    Fc = Cc :=
  B.facetPrecedes_antisymm
    (E.facetPrecedes_of_buildingZeroFixer_le B hne' hΩ' hne hΩ heq.ge)
    (E.facetPrecedes_of_buildingZeroFixer_le B hne hΩ hne' hΩ' heq.le)

/-- The actual generic zero-fixer subgroup faithfully encodes every full
facet of the maximal-unramified building. -/
def buildingFacetZeroFixerEmbedding :
    B.BuildingFacet ↪ Subgroup (rationalPoints H) where
  toFun Fc := E.zeroPoints ⊓ B.pointwiseFixer Fc.val
  inj' := fun Fc Cc heq => E.buildingFacet_eq_of_zeroFixer_eq B
    (Fc.property.nonempty B) (Set.Subset.refl _)
    (Cc.property.nonempty B) (Set.Subset.refl _) heq

@[simp] theorem buildingFacetZeroFixerEmbedding_apply (Fc : B.BuildingFacet) :
    E.buildingFacetZeroFixerEmbedding B Fc =
      E.zeroPoints ⊓ B.pointwiseFixer Fc.val :=
  rfl

end UnramifiedZeroDatum
end Langlands.Geometry.Building
