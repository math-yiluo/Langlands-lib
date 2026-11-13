import Langlands.Geometry.Building.BuildingFacetIncidence
import Langlands.Geometry.Building.BuildingFacetPartition
import Langlands.Geometry.Building.AffineWeylFacetFixing

/-! # Chambers and facet incidence in the actual valuation quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

namespace AffineRootSystem

variable {V A : Type u} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)} {Ca Fa : Set A}

/-- A chamber that is a face of a facet is that facet. -/
theorem IsFaceOf.eq_of_isChamber (hCF : IsFaceOf Ψ Ca Fa) (hC : IsChamber Ψ Ca) :
    Ca = Fa := by
  obtain ⟨c, hc, rfl⟩ := hC
  obtain ⟨_, f, hf, hcf⟩ := hCF
  have hcf' := hcf (mem_facet_self Ψ c)
  have hrel : facetRel Ψ c f := by
    intro ψ hψ
    exact (hcf' ψ hψ).resolve_left (by
      simpa only [sign_eq_zero_iff] using hc ψ hψ)
  exact (facet_eq_facet_iff.2 hrel).trans hf

/-- Every facet is a face of a chamber of a locally finite reflection arrangement. -/
theorem IsFacet.exists_isChamber_isFaceOf (hF : IsFacet Ψ Fa)
    (hΨ : IsLocallyFiniteReflectionArrangement Ψ) :
    ∃ Ca : Set A, IsChamber Ψ Ca ∧ IsFaceOf Ψ Fa Ca := by
  obtain ⟨f, rfl⟩ := hF
  obtain ⟨c, hc, hfc⟩ := hΨ.exists_regularPoint_closure f
  exact ⟨facet Ψ c, ⟨c, hc, rfl⟩, isFacet_facet Ψ f, c, rfl,
    facet_subset_facetClosure_iff.2 hfc⟩

end AffineRootSystem

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- Chamberhood of a facet image is reflected by every translated apartment chart.
The actual quotient relation transports a chamber to the chosen coordinates. -/
theorem isChamber_translatedApartmentMap_image_iff
    (hD : B.SatisfiesApartmentAxioms)
    (g : rationalPoints G) {Ca : Set B.Apartment}
    (hCa : AffineRootSystem.IsFacet B.affineRoots Ca) :
    B.IsChamber (B.translatedApartmentMap g '' Ca) ↔
      AffineRootSystem.IsChamber B.affineRoots Ca := by
  constructor
  · rintro ⟨h, Da, hDa, himage⟩
    obtain ⟨a, ha⟩ := hDa.nonempty
    have hpoint : h • B.apartmentMap a ∈ B.translatedApartmentMap g '' Ca := by
      rw [himage]
      exact ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hba⟩ := hpoint
    have hab : (g⁻¹ * h) • B.apartmentMap a = B.apartmentMap b := by
      change g • B.apartmentMap b = h • B.apartmentMap a at hba
      rw [mul_smul, ← hba, inv_smul_smul]
    obtain ⟨n, hn, _⟩ :=
      B.exists_normalizer_eq_on_translated_facet hD hDa.isFacet ha (g⁻¹ * h) hab
    have hnDa : n • Da = Ca :=
      (B.normalizer_smul_isFacet hD hDa.isFacet n).eq_of_mem_mem hCa
        (hn ▸ Set.smul_mem_smul_set ha) hb
    have hnC : AffineRootSystem.IsChamber B.affineRoots (n • Da) :=
      hDa.image (hD.range_le_extendedAffineWeylGroup ⟨n, rfl⟩).1
    rwa [hnDa] at hnC
  · intro hC
    exact ⟨g, Ca, hC, rfl⟩

/-- An original building facet above a chamber in the face order is that chamber. -/
theorem eq_of_isChamber_of_facetPrecedes
    (hD : B.SatisfiesApartmentAxioms)
    {Cc Fc : BuildingFacet B} (hC : B.IsChamber Cc.val)
    (hCF : FacetPrecedes B Cc Fc) : Cc = Fc := by
  obtain ⟨g, Ca, Fa, hCFa, hCimage, hFimage⟩ := hCF
  rw [hCimage] at hC
  have hCa := (B.isChamber_translatedApartmentMap_image_iff hD g hCFa.1).mp hC
  apply Subtype.ext
  exact hCimage.trans ((congrArg (B.translatedApartmentMap g '' ·)
    (hCFa.eq_of_isChamber hCa)).trans hFimage.symm)

/-- Every original building facet has an incident chamber above it. -/
theorem exists_isChamber_facetPrecedes
    (hD : B.SatisfiesApartmentAxioms) (Fc : BuildingFacet B) :
    ∃ Cc : BuildingFacet B, B.IsChamber Cc.val ∧ FacetPrecedes B Fc Cc := by
  obtain ⟨g, Fa, hFa, hFimage⟩ := Fc.property
  obtain ⟨Ca, hCa, hFCa⟩ := hFa.exists_isChamber_isFaceOf
    hD.isAffineRootSystem_affineRoots.isLocallyFiniteReflectionArrangement
  let Cc : BuildingFacet B :=
    ⟨B.translatedApartmentMap g '' Ca, g, Ca, hCa.isFacet, rfl⟩
  exact ⟨Cc, ⟨g, Ca, hCa, rfl⟩, g, Fa, Ca, hFCa, hFimage, rfl⟩

/-- Choose an incident chamber in the original building, retaining chamberhood
and the original facet-incidence predicate. -/
def incidentChamber
    (hD : B.SatisfiesApartmentAxioms) (Fc : BuildingFacet B) :
    {Cc : BuildingFacet B // B.IsChamber Cc.val ∧ FacetPrecedes B Fc Cc} :=
  ⟨(B.exists_isChamber_facetPrecedes hD Fc).choose,
    (B.exists_isChamber_facetPrecedes hD Fc).choose_spec⟩

end ValuationBuildingData
end Langlands.Geometry.Building
