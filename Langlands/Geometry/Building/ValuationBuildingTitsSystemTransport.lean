import Langlands.Geometry.Building.FullValidity.ChamberAxioms
import Langlands.Geometry.Building.ValuationBuildingRealizationTransport
import Langlands.Group.TitsSystemEquiv

/-! # Tits-system comparison on actual valuation quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Group Langlands.Group.TitsSystem
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P₁ P₂ : ParahoricBuildingData G)
  (hzero : P₁.zeroSubgroup = P₂.zeroSubgroup)

section Normalizer

variable (σ : P₁.S ≅ P₂.S)
  (hσ : P₁.i = CommGroupScheme.groupHom σ.hom ≫ P₂.i)

include hσ in
/-- The entire actual normalizer restricted to the supplied zero subgroup is transported. -/
theorem normalizerInZero_map_of_torusIso :
    P₁.normalizerInZero.map (MulEquiv.subgroupCongr hzero).toMonoidHom = P₂.normalizerInZero := by
  have hN := ValuationBuildingData.normalizerPoints_eq_of_torusIso
    P₁.toValuationBuildingData P₂.toValuationBuildingData σ hσ
  ext g
  constructor
  · rintro ⟨n, hn, rfl⟩
    change (n : rationalPoints G) ∈ normalizerPoints P₂.i
    rw [← hN]
    exact hn
  · intro hg
    refine ⟨(MulEquiv.subgroupCongr hzero).symm g, ?_, (MulEquiv.subgroupCongr hzero).apply_symm_apply g⟩
    change (g : rationalPoints G) ∈ normalizerPoints P₁.i
    rw [hN]
    exact hg

/-- The source Weyl projection transported through the full actual normalizer comparison. -/
def titsProjectionOfComparison {W : Type u} [Group W]
    (π : P₁.normalizerInZero →* W) : P₂.normalizerInZero →* W :=
  equivProjection (MulEquiv.subgroupCongr hzero) P₁.normalizerInZero P₂.normalizerInZero
    (normalizerInZero_map_of_torusIso P₁ P₂ hzero σ hσ) π

end Normalizer

section Equivariant

variable (Φ : P₁.ReducedBuilding ≃ P₂.ReducedBuilding)
  (hΦ : ∀ (g : rationalPoints G) (q : P₁.ReducedBuilding), Φ (g • q) = g • Φ q)

include hΦ

/-- The full set stabilizers in the supplied zero subgroups correspond under the comparison. -/
theorem zeroStabilizerIn_map_of_equivariantEquiv (Y : Set P₁.ReducedBuilding) :
    (P₁.zeroStabilizerIn Y).map (MulEquiv.subgroupCongr hzero).toMonoidHom = P₂.zeroStabilizerIn (Φ '' Y) := by
  ext g
  constructor
  · rintro ⟨n, hn, rfl⟩
    change (n : rationalPoints G) • (Φ '' Y) = Φ '' Y
    rw [← ValuationBuildingData.image_smul_of_equivariantEquiv
      P₁.toValuationBuildingData P₂.toValuationBuildingData Φ hΦ]
    rw [P₁.mem_zeroStabilizerIn.mp hn]
  · intro hg
    refine ⟨(MulEquiv.subgroupCongr hzero).symm g, ?_, (MulEquiv.subgroupCongr hzero).apply_symm_apply g⟩
    change (g : rationalPoints G) • Y = Y
    apply Φ.injective.image_injective
    rw [ValuationBuildingData.image_smul_of_equivariantEquiv
      P₁.toValuationBuildingData P₂.toValuationBuildingData Φ hΦ]
    exact hg

variable (hiso : ValuationBuildingData.IsBuildingIso
  P₁.toValuationBuildingData P₂.toValuationBuildingData Φ)

/-- The actual facet stabilizer map commutes with the full facet equivalence. -/
theorem facetZeroStabilizer_map_of_buildingIso
    (Fc : BuildingFacet P₁.toValuationBuildingData) :
    (P₁.facetZeroStabilizer Fc).map (MulEquiv.subgroupCongr hzero).toMonoidHom =
      P₂.facetZeroStabilizer
        (hiso.facetEquiv P₁.toValuationBuildingData P₂.toValuationBuildingData Φ Fc) :=
  zeroStabilizerIn_map_of_equivariantEquiv P₁ P₂ hzero Φ hΦ Fc.val

variable (e : P₁.Apartment ≃ᵃ[ℝ] P₂.Apartment)
  (hmap : ∀ x : P₁.Apartment, Φ (P₁.apartmentMap x) = P₂.apartmentMap (e x))

include e hmap in
/-- The actual chamber stabilizer is the full transported Iwahori subgroup. -/
theorem chamberZeroStabilizerIn_map_of_comparison (Ca : Set P₁.Apartment) :
    (P₁.chamberZeroStabilizerIn Ca).map (MulEquiv.subgroupCongr hzero).toMonoidHom =
      P₂.chamberZeroStabilizerIn (e '' Ca) := by
  have himage : Φ '' (P₁.apartmentMap '' Ca) = P₂.apartmentMap '' (e '' Ca) := by
    rw [Set.image_image, Set.image_image]
    congr 1
    funext x
    exact hmap x
  simpa only [chamberZeroStabilizerIn, himage] using
    zeroStabilizerIn_map_of_equivariantEquiv P₁ P₂ hzero Φ hΦ (P₁.apartmentMap '' Ca)

include hiso e hmap in
/-- Every translated apartment retains precisely all its facet stabilizers. -/
theorem image_apartmentFacetStabilizersAt_of_comparison (g : rationalPoints G) :
    (fun Q : Subgroup P₁.zeroSubgroup => Q.map (MulEquiv.subgroupCongr hzero).toMonoidHom) ''
        (P₁.facetZeroStabilizer ''
          {Fc | Fc.val ⊆ g • P₁.apartmentImage}) =
      P₂.facetZeroStabilizer '' {Fc | Fc.val ⊆ g • P₂.apartmentImage} := by
  let f := hiso.facetEquiv P₁.toValuationBuildingData P₂.toValuationBuildingData Φ
  have hsub (Fc : BuildingFacet P₁.toValuationBuildingData) :
      (f Fc).val ⊆ g • P₂.apartmentImage ↔ Fc.val ⊆ g • P₁.apartmentImage := by
    change Φ '' Fc.val ⊆ g • P₂.apartmentImage ↔ _
    rw [← ValuationBuildingData.image_apartmentImage_of_comparison
      P₁.toValuationBuildingData P₂.toValuationBuildingData Φ e hmap,
      ← ValuationBuildingData.image_smul_of_equivariantEquiv
        P₁.toValuationBuildingData P₂.toValuationBuildingData Φ hΦ]
    exact Set.image_subset_image_iff Φ.injective
  ext Q
  constructor
  · rintro ⟨_, ⟨Fc, hFc, rfl⟩, rfl⟩
    exact ⟨f Fc, (hsub Fc).2 hFc,
      (facetZeroStabilizer_map_of_buildingIso P₁ P₂ hzero Φ hΦ hiso Fc).symm⟩
  · rintro ⟨Fc, hFc, rfl⟩
    obtain ⟨Fc, rfl⟩ := f.surjective Fc
    refine ⟨P₁.facetZeroStabilizer Fc, ⟨Fc, (hsub Fc).1 hFc, rfl⟩, ?_⟩
    exact facetZeroStabilizer_map_of_buildingIso P₁ P₂ hzero Φ hΦ hiso Fc

include hiso e hmap in
/-- The entire sets of apartments, represented by their full sets of facet stabilizers, agree. -/
theorem image_apartmentFacetStabilizers_of_comparison :
    (fun Qs : Set (Subgroup P₁.zeroSubgroup) =>
      (fun Q => Q.map (MulEquiv.subgroupCongr hzero).toMonoidHom) '' Qs) '' P₁.apartmentFacetStabilizers =
        P₂.apartmentFacetStabilizers := by
  ext Qs
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, image_apartmentFacetStabilizersAt_of_comparison
      P₁ P₂ hzero Φ hΦ hiso e hmap g⟩
  · rintro ⟨g, rfl⟩
    exact ⟨_, ⟨g, rfl⟩, image_apartmentFacetStabilizersAt_of_comparison
      P₁ P₂ hzero Φ hΦ hiso e hmap g⟩

variable (hroots : AffineRootSystem.transportedRoots e P₁.affineRoots = P₂.affineRoots)
  (σ : P₁.S ≅ P₂.S)
  (hσ : P₁.i = CommGroupScheme.groupHom σ.hom ≫ P₂.i)

include hzero hiso e hmap hroots hσ

/-- All six clauses of the actual building Tits-system predicate transport together. -/
theorem isBuildingTitsSystem_of_comparison {Ca : Set P₁.Apartment}
    {W : Type u} [Group W] {π : P₁.normalizerInZero →* W} {Sgen : Set W}
    (h : P₁.IsBuildingTitsSystem Ca π Sgen) :
    P₂.IsBuildingTitsSystem (e '' Ca)
      (titsProjectionOfComparison P₁ P₂ hzero σ hσ π) Sgen := by
  let f := hiso.facetEquiv P₁.toValuationBuildingData P₂.toValuationBuildingData Φ
  have hN := normalizerInZero_map_of_torusIso P₁ P₂ hzero σ hσ
  have hC := chamberZeroStabilizerIn_map_of_comparison P₁ P₂ hzero Φ hΦ e hmap Ca
  have hAdm (Q : Subgroup P₁.zeroSubgroup) :
      IsAdmissibleParabolic (P₂.chamberZeroStabilizerIn (e '' Ca))
        (titsProjectionOfComparison P₁ P₂ hzero σ hσ π) Sgen
        (Q.map (MulEquiv.subgroupCongr hzero).toMonoidHom) ↔
      IsAdmissibleParabolic (P₁.chamberZeroStabilizerIn Ca) π Sgen Q := by
    rw [← hC]
    exact isAdmissibleParabolic_map_equiv_iff (MulEquiv.subgroupCongr hzero) P₁.normalizerInZero
      P₂.normalizerInZero hN (P₁.chamberZeroStabilizerIn Ca) π Sgen Q
  refine
    { isTitsSystem := ?_
      finite := h.finite
      isSaturated := ?_
      bijOn_facetZeroStabilizer := ?_
      facetPrecedes_iff := ?_
      apartmentFacetStabilizers_eq := ?_ }
  · simpa only [hC, titsProjectionOfComparison] using isTitsSystem_equiv (MulEquiv.subgroupCongr hzero) P₁.normalizerInZero
      P₂.normalizerInZero hN (P₁.chamberZeroStabilizerIn Ca) π h.isTitsSystem
  · simpa only [hC, titsProjectionOfComparison] using isSaturated_equiv (MulEquiv.subgroupCongr hzero) P₁.normalizerInZero
      P₂.normalizerInZero hN (P₁.chamberZeroStabilizerIn Ca) h.isSaturated
  · refine ⟨?_, ?_, ?_⟩
    · intro Fc _
      obtain ⟨Fc, rfl⟩ := f.surjective Fc
      rw [← facetZeroStabilizer_map_of_buildingIso P₁ P₂ hzero Φ hΦ hiso Fc]
      exact (hAdm _).2 (h.bijOn_facetZeroStabilizer.mapsTo (Set.mem_univ Fc))
    · intro Fc _ Fc' _ heq
      obtain ⟨Fc, rfl⟩ := f.surjective Fc
      obtain ⟨Fc', rfl⟩ := f.surjective Fc'
      apply congrArg f
      apply h.bijOn_facetZeroStabilizer.injOn (Set.mem_univ _) (Set.mem_univ _)
      apply Subgroup.map_injective (f := (MulEquiv.subgroupCongr hzero).toMonoidHom)
        (MulEquiv.subgroupCongr hzero).injective
      simpa only [facetZeroStabilizer_map_of_buildingIso P₁ P₂ hzero Φ hΦ hiso] using heq
    · intro Q' hQ'
      let Q := Q'.comap (MulEquiv.subgroupCongr hzero).toMonoidHom
      have hQ : Q.map (MulEquiv.subgroupCongr hzero).toMonoidHom = Q' :=
        Subgroup.map_comap_eq_self_of_surjective (MulEquiv.subgroupCongr hzero).surjective Q'
      have hAQ : IsAdmissibleParabolic (P₁.chamberZeroStabilizerIn Ca) π Sgen Q :=
        (hAdm Q).1 (by simpa only [hQ, Set.mem_ofPred_eq] using hQ')
      obtain ⟨Fc, _, hFc⟩ := h.bijOn_facetZeroStabilizer.surjOn hAQ
      refine ⟨f Fc, Set.mem_univ _, ?_⟩
      rw [← facetZeroStabilizer_map_of_buildingIso P₁ P₂ hzero Φ hΦ hiso Fc, hFc, hQ]
  · intro Fc Fc'
    obtain ⟨Fc, rfl⟩ := f.surjective Fc
    obtain ⟨Fc', rfl⟩ := f.surjective Fc'
    rw [ValuationBuildingData.facetPrecedes_facetEquiv_iff
      P₁.toValuationBuildingData P₂.toValuationBuildingData Φ hiso hΦ e hmap hroots,
      h.facetPrecedes_iff,
      ← facetZeroStabilizer_map_of_buildingIso P₁ P₂ hzero Φ hΦ hiso Fc,
      ← facetZeroStabilizer_map_of_buildingIso P₁ P₂ hzero Φ hΦ hiso Fc']
    exact (Subgroup.map_le_map_iff_of_injective (MulEquiv.subgroupCongr hzero).injective).symm
  · rw [← image_apartmentFacetStabilizers_of_comparison P₁ P₂ hzero Φ hΦ hiso e hmap,
      h.apartmentFacetStabilizers_eq]
    simpa only [hC, titsProjectionOfComparison] using image_restrictedApartments_equiv (MulEquiv.subgroupCongr hzero) P₁.normalizerInZero
      P₂.normalizerInZero hN (P₁.chamberZeroStabilizerIn Ca) π Sgen

/-- KP 4.1.9 transports for every actual target chamber with its source Weyl group in Type u. -/
theorem hasTitsSystem_of_comparison (hP : P₁.HasTitsSystem) : P₂.HasTitsSystem := by
  intro Ca hCa
  let Ca₁ := e.symm '' Ca
  have hCaimage : e '' Ca₁ = Ca := by
    change e '' (e.symm '' Ca) = Ca
    rw [Set.image_image]
    simp only [e.apply_symm_apply, Set.image_id']
  have hCa₁ : AffineRootSystem.IsChamber P₁.affineRoots Ca₁ := by
    apply (AffineRootSystem.isChamber_image_transportedRoots_iff e P₁.affineRoots Ca₁).1
    simpa only [hroots, hCaimage] using hCa
  obtain ⟨W, instW, π, Sgen, h⟩ := hP Ca₁ hCa₁
  let := instW
  refine ⟨W, instW, titsProjectionOfComparison P₁ P₂ hzero σ hσ π, Sgen, ?_⟩
  simpa only [hCaimage] using
    isBuildingTitsSystem_of_comparison P₁ P₂ hzero Φ hΦ hiso e hmap hroots σ hσ h

end Equivariant

end Langlands.Geometry.Building.ParahoricBuildingData
