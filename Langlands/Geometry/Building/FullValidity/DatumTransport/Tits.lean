import Langlands.Geometry.Building.FullValidity.DatumTransport.RootGroups
import Langlands.Geometry.Building.FullValidity.DatumTransport.Realization
import Langlands.Geometry.Building.ValuationBuildingTitsSystemTransport

/-!
# Axiom 4.1.9 under based group isomorphisms

A building isomorphism `Φ : B(G₁) ≃ B(G₂)` that is equivariant for an isomorphism
`φ : G₁(F) ≃* G₂(F)`, compatible with an affine comparison of the apartments matching the affine
roots, and with `φ(G₁(F)^0) = G₂(F)^0` and `φ(N₁(F)) = N₂(F)`, carries the Tits system of KP
Axiom 4.1.9 for `G₁` to one for `G₂`. The proof follows the Library's same-group comparison
`ValuationBuildingTitsSystemTransport`; here the two groups differ. The transported data of `H`
satisfy these hypotheses.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Group Langlands.Group.TitsSystem
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

open DatumTransport

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G₁ G₂ : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G₁.X.hom]
  [IsAffineHom G₂.X.hom]
  {B₁ : ValuationBuildingData G₁} {B₂ : ValuationBuildingData G₂}
  (Φ : B₁.ReducedBuilding ≃ B₂.ReducedBuilding) (A : B₁.Apartment ≃ᵃ[ℝ] B₂.Apartment)
  (hmap : ∀ x : B₁.Apartment, Φ (B₁.apartmentMap x) = B₂.apartmentMap (A x))

include hmap in
/-- The standard apartment is carried onto the standard apartment. -/
theorem image_apartmentImage_of_apartmentMap : Φ '' B₁.apartmentImage = B₂.apartmentImage := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨A x, (hmap x).symm⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := A.surjective x
    exact ⟨B₁.apartmentMap x, ⟨x, rfl⟩, hmap x⟩

end ValuationBuildingData

namespace ParahoricBuildingData

/-! ### Comparison of Tits systems between two groups -/

section Comparison

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G₁ G₂ : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G₁.X.hom]
  [IsAffineHom G₂.X.hom]
  (P₁ : ParahoricBuildingData G₁) (P₂ : ParahoricBuildingData G₂)
  (φ : rationalPoints G₁ ≃* rationalPoints G₂)
  (hzero : P₁.zeroSubgroup.map φ.toMonoidHom = P₂.zeroSubgroup)

/-- The isomorphism `G₁(F)^0 ≃* G₂(F)^0` induced by `φ`. -/
def zeroSubgroupEquiv : P₁.zeroSubgroup ≃* P₂.zeroSubgroup :=
  equivNormalizer φ P₁.zeroSubgroup P₂.zeroSubgroup hzero

@[simp] theorem coe_zeroSubgroupEquiv (g : P₁.zeroSubgroup) :
    (zeroSubgroupEquiv P₁ P₂ φ hzero g : rationalPoints G₂) = φ g := rfl

section Normalizer

variable (hN : ∀ g : rationalPoints G₁, φ g ∈ normalizerPoints P₂.i ↔ g ∈ normalizerPoints P₁.i)

include hN in
/-- `N₁(F) ∩ G₁(F)^0` is carried onto `N₂(F) ∩ G₂(F)^0`. -/
theorem normalizerInZero_map_zeroSubgroupEquiv :
    P₁.normalizerInZero.map (zeroSubgroupEquiv P₁ P₂ φ hzero).toMonoidHom =
      P₂.normalizerInZero := by
  ext g
  constructor
  · rintro ⟨n, hn, rfl⟩
    change φ (n : rationalPoints G₁) ∈ normalizerPoints P₂.i
    exact (hN n).2 hn
  · intro hg
    refine ⟨(zeroSubgroupEquiv P₁ P₂ φ hzero).symm g, ?_,
      (zeroSubgroupEquiv P₁ P₂ φ hzero).apply_symm_apply g⟩
    change (((zeroSubgroupEquiv P₁ P₂ φ hzero).symm g : P₁.zeroSubgroup) : rationalPoints G₁) ∈
      normalizerPoints P₁.i
    apply (hN _).1
    rw [← coe_zeroSubgroupEquiv P₁ P₂ φ hzero, MulEquiv.apply_symm_apply]
    exact hg

/-- The Weyl-group datum of `G₁` read on `N₂(F) ∩ G₂(F)^0`. -/
def titsProjectionOfIso {W : Type u} [Group W] (π : P₁.normalizerInZero →* W) :
    P₂.normalizerInZero →* W :=
  equivProjection (zeroSubgroupEquiv P₁ P₂ φ hzero) P₁.normalizerInZero P₂.normalizerInZero
    (normalizerInZero_map_zeroSubgroupEquiv P₁ P₂ φ hzero hN) π

end Normalizer

section Equivariant

variable (Φ : P₁.ReducedBuilding ≃ P₂.ReducedBuilding)
  (hsmul : ∀ (g : rationalPoints G₁) (q : P₁.ReducedBuilding), Φ (g • q) = φ g • Φ q)

include hsmul

/-- Stabilizers in the zero subgroups correspond. -/
theorem zeroStabilizerIn_map_zeroSubgroupEquiv (Y : Set P₁.ReducedBuilding) :
    (P₁.zeroStabilizerIn Y).map (zeroSubgroupEquiv P₁ P₂ φ hzero).toMonoidHom =
      P₂.zeroStabilizerIn (Φ '' Y) := by
  ext g
  constructor
  · rintro ⟨n, hn, rfl⟩
    change φ (n : rationalPoints G₁) • (Φ '' Y) = Φ '' Y
    rw [← ValuationBuildingData.image_smul_of_equivariant Φ φ hsmul,
      P₁.mem_zeroStabilizerIn.mp hn]
  · intro hg
    refine ⟨(zeroSubgroupEquiv P₁ P₂ φ hzero).symm g, ?_,
      (zeroSubgroupEquiv P₁ P₂ φ hzero).apply_symm_apply g⟩
    change (((zeroSubgroupEquiv P₁ P₂ φ hzero).symm g : P₁.zeroSubgroup) : rationalPoints G₁) •
      Y = Y
    apply Φ.injective.image_injective
    rw [ValuationBuildingData.image_smul_of_equivariant Φ φ hsmul,
      ← coe_zeroSubgroupEquiv P₁ P₂ φ hzero, MulEquiv.apply_symm_apply]
    exact hg

variable (hiso : ValuationBuildingData.IsBuildingIso
  P₁.toValuationBuildingData P₂.toValuationBuildingData Φ)

/-- Facet stabilizers correspond under the facet bijection. -/
theorem facetZeroStabilizer_map_zeroSubgroupEquiv
    (Fc : BuildingFacet P₁.toValuationBuildingData) :
    (P₁.facetZeroStabilizer Fc).map (zeroSubgroupEquiv P₁ P₂ φ hzero).toMonoidHom =
      P₂.facetZeroStabilizer (ValuationBuildingData.facetEquivOfIsBuildingIso Φ hiso Fc) :=
  zeroStabilizerIn_map_zeroSubgroupEquiv P₁ P₂ φ hzero Φ hsmul Fc.val

variable (A : P₁.Apartment ≃ᵃ[ℝ] P₂.Apartment)
  (hmap : ∀ x : P₁.Apartment, Φ (P₁.apartmentMap x) = P₂.apartmentMap (A x))

include hmap in
/-- Iwahori subgroups of chambers of the apartments correspond. -/
theorem chamberZeroStabilizerIn_map_zeroSubgroupEquiv (Ca : Set P₁.Apartment) :
    (P₁.chamberZeroStabilizerIn Ca).map (zeroSubgroupEquiv P₁ P₂ φ hzero).toMonoidHom =
      P₂.chamberZeroStabilizerIn (A '' Ca) := by
  have himage : Φ '' (P₁.apartmentMap '' Ca) = P₂.apartmentMap '' (A '' Ca) := by
    rw [Set.image_image, Set.image_image]
    exact Set.image_congr fun x _ => hmap x
  simpa only [chamberZeroStabilizerIn, himage] using
    zeroStabilizerIn_map_zeroSubgroupEquiv P₁ P₂ φ hzero Φ hsmul (P₁.apartmentMap '' Ca)

include hiso hmap in
/-- The facet stabilizers in the apartment `g · A₁` correspond to those in `φ(g) · A₂`. -/
theorem image_apartmentFacetStabilizersAt_zeroSubgroupEquiv (g : rationalPoints G₁) :
    (fun Q : Subgroup P₁.zeroSubgroup =>
        Q.map (zeroSubgroupEquiv P₁ P₂ φ hzero).toMonoidHom) ''
        (P₁.facetZeroStabilizer '' {Fc | Fc.val ⊆ g • P₁.apartmentImage}) =
      P₂.facetZeroStabilizer '' {Fc | Fc.val ⊆ φ g • P₂.apartmentImage} := by
  let fe := ValuationBuildingData.facetEquivOfIsBuildingIso Φ hiso
  have hsub (Fc : BuildingFacet P₁.toValuationBuildingData) :
      (fe Fc).val ⊆ φ g • P₂.apartmentImage ↔ Fc.val ⊆ g • P₁.apartmentImage := by
    change Φ '' Fc.val ⊆ φ g • P₂.apartmentImage ↔ _
    rw [← ValuationBuildingData.image_apartmentImage_of_apartmentMap Φ A hmap,
      ← ValuationBuildingData.image_smul_of_equivariant Φ φ hsmul]
    exact Set.image_subset_image_iff Φ.injective
  ext Q
  constructor
  · rintro ⟨_, ⟨Fc, hFc, rfl⟩, rfl⟩
    exact ⟨fe Fc, (hsub Fc).2 hFc,
      (facetZeroStabilizer_map_zeroSubgroupEquiv P₁ P₂ φ hzero Φ hsmul hiso Fc).symm⟩
  · rintro ⟨Fc, hFc, rfl⟩
    obtain ⟨Fc, rfl⟩ := fe.surjective Fc
    exact ⟨P₁.facetZeroStabilizer Fc, ⟨Fc, (hsub Fc).1 hFc, rfl⟩,
      facetZeroStabilizer_map_zeroSubgroupEquiv P₁ P₂ φ hzero Φ hsmul hiso Fc⟩

include hiso hmap in
/-- The apartments, as sets of facet stabilizers, correspond. -/
theorem image_apartmentFacetStabilizers_zeroSubgroupEquiv :
    (fun Qs : Set (Subgroup P₁.zeroSubgroup) =>
      (fun Q => Q.map (zeroSubgroupEquiv P₁ P₂ φ hzero).toMonoidHom) '' Qs) ''
        P₁.apartmentFacetStabilizers = P₂.apartmentFacetStabilizers := by
  ext Qs
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨φ g, image_apartmentFacetStabilizersAt_zeroSubgroupEquiv P₁ P₂ φ hzero Φ hsmul hiso
      A hmap g⟩
  · rintro ⟨g', rfl⟩
    obtain ⟨g, rfl⟩ := φ.surjective g'
    exact ⟨_, ⟨g, rfl⟩, image_apartmentFacetStabilizersAt_zeroSubgroupEquiv P₁ P₂ φ hzero Φ
      hsmul hiso A hmap g⟩

variable
  (hchart : ∀ g x, Φ (P₁.translatedApartmentMap g x) = P₂.translatedApartmentMap (φ g) (A x))
  (hroots : AffineRootSystem.transportedRoots A P₁.affineRoots = P₂.affineRoots)
  (hN : ∀ g : rationalPoints G₁, φ g ∈ normalizerPoints P₂.i ↔ g ∈ normalizerPoints P₁.i)

include hzero hiso hmap hchart hroots hN

/-- All clauses of KP Axiom 4.1.9 at a chamber are carried to the image chamber. -/
theorem isBuildingTitsSystem_of_iso {Ca : Set P₁.Apartment}
    {W : Type u} [Group W] {π : P₁.normalizerInZero →* W} {Sgen : Set W}
    (h : P₁.IsBuildingTitsSystem Ca π Sgen) :
    P₂.IsBuildingTitsSystem (A '' Ca) (titsProjectionOfIso P₁ P₂ φ hzero hN π) Sgen := by
  let fe := ValuationBuildingData.facetEquivOfIsBuildingIso Φ hiso
  let ζ := zeroSubgroupEquiv P₁ P₂ φ hzero
  have hNz := normalizerInZero_map_zeroSubgroupEquiv P₁ P₂ φ hzero hN
  have hC := chamberZeroStabilizerIn_map_zeroSubgroupEquiv P₁ P₂ φ hzero Φ hsmul A hmap Ca
  have hF := facetZeroStabilizer_map_zeroSubgroupEquiv P₁ P₂ φ hzero Φ hsmul hiso
  have hAdm (Q : Subgroup P₁.zeroSubgroup) :
      IsAdmissibleParabolic (P₂.chamberZeroStabilizerIn (A '' Ca))
        (titsProjectionOfIso P₁ P₂ φ hzero hN π) Sgen (Q.map ζ.toMonoidHom) ↔
      IsAdmissibleParabolic (P₁.chamberZeroStabilizerIn Ca) π Sgen Q := by
    rw [← hC]
    exact isAdmissibleParabolic_map_equiv_iff ζ P₁.normalizerInZero P₂.normalizerInZero hNz
      (P₁.chamberZeroStabilizerIn Ca) π Sgen Q
  refine
    { isTitsSystem := ?_
      finite := h.finite
      isSaturated := ?_
      bijOn_facetZeroStabilizer := ?_
      facetPrecedes_iff := ?_
      apartmentFacetStabilizers_eq := ?_ }
  · rw [← hC]
    exact isTitsSystem_equiv ζ P₁.normalizerInZero P₂.normalizerInZero hNz
      (P₁.chamberZeroStabilizerIn Ca) π h.isTitsSystem
  · rw [← hC]
    exact isSaturated_equiv ζ P₁.normalizerInZero P₂.normalizerInZero hNz
      (P₁.chamberZeroStabilizerIn Ca) h.isSaturated
  · refine ⟨?_, ?_, ?_⟩
    · intro Fc _
      obtain ⟨Fc, rfl⟩ := fe.surjective Fc
      rw [← hF Fc]
      exact (hAdm _).2 (h.bijOn_facetZeroStabilizer.mapsTo (Set.mem_univ Fc))
    · intro Fc _ Fc' _ heq
      obtain ⟨Fc, rfl⟩ := fe.surjective Fc
      obtain ⟨Fc', rfl⟩ := fe.surjective Fc'
      apply congrArg fe
      apply h.bijOn_facetZeroStabilizer.injOn (Set.mem_univ _) (Set.mem_univ _)
      apply Subgroup.map_injective (f := ζ.toMonoidHom) ζ.injective
      rw [hF, hF]
      exact heq
    · intro Q' hQ'
      let Q := Q'.comap ζ.toMonoidHom
      have hQ : Q.map ζ.toMonoidHom = Q' :=
        Subgroup.map_comap_eq_self_of_surjective ζ.surjective Q'
      have hAQ : IsAdmissibleParabolic (P₁.chamberZeroStabilizerIn Ca) π Sgen Q :=
        (hAdm Q).1 (by rw [hQ]; exact hQ')
      obtain ⟨Fc, _, hFc⟩ := h.bijOn_facetZeroStabilizer.surjOn hAQ
      refine ⟨fe Fc, Set.mem_univ _, ?_⟩
      rw [← hF Fc, hFc, hQ]
  · intro Fc Fc'
    obtain ⟨Fc, rfl⟩ := fe.surjective Fc
    obtain ⟨Fc', rfl⟩ := fe.surjective Fc'
    rw [ValuationBuildingData.facetPrecedes_facetEquiv_iff_of_chart Φ hiso φ A hchart hroots,
      h.facetPrecedes_iff, ← hF Fc, ← hF Fc']
    exact (Subgroup.map_le_map_iff_of_injective ζ.injective).symm
  · rw [← image_apartmentFacetStabilizers_zeroSubgroupEquiv P₁ P₂ φ hzero Φ hsmul hiso A hmap,
      h.apartmentFacetStabilizers_eq]
    rw [← hC]
    exact image_restrictedApartments_equiv ζ P₁.normalizerInZero P₂.normalizerInZero hNz
      (P₁.chamberZeroStabilizerIn Ca) π Sgen

/-- KP Axiom 4.1.9 for `G₁` gives Axiom 4.1.9 for `G₂`. -/
theorem hasTitsSystem_of_iso (hP : P₁.HasTitsSystem) : P₂.HasTitsSystem := by
  intro Ca hCa
  let Ca₁ := A.symm '' Ca
  have hCaimage : A '' Ca₁ = Ca := affineEquiv_image_symm_image A Ca
  have hCa₁ : AffineRootSystem.IsChamber P₁.affineRoots Ca₁ := by
    apply (AffineRootSystem.isChamber_image_transportedRoots_iff A P₁.affineRoots Ca₁).1
    rw [hroots, hCaimage]
    exact hCa
  obtain ⟨W, instW, π, Sgen, h⟩ := hP Ca₁ hCa₁
  refine ⟨W, instW, titsProjectionOfIso P₁ P₂ φ hzero hN π, Sgen, ?_⟩
  have h' := isBuildingTitsSystem_of_iso P₁ P₂ φ hzero Φ hsmul hiso A hmap hchart hroots hN h
  rwa [hCaimage] at h'

end Equivariant

end Comparison

/-! ### The transported data -/

section Transport

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (P : ParahoricBuildingData G) {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {j : S.toGrp ⟶ H} (σ : P.S ≅ S) (f : G ≅ H)
  (h : P.i ≫ f.hom = CommGroupScheme.groupHom σ.hom ≫ j)

/-- `G(F)^0` is carried onto `H(F)^0` by the points isomorphism. -/
theorem map_zeroSubgroup_pointsEquiv :
    P.zeroSubgroup.map (pointsEquiv f).toMonoidHom = (P.basedTransport σ f h).zeroSubgroup :=
  (P.basedTransport_zeroSubgroup σ f h).symm

/-- KP Axiom 4.1.9 for `G` gives Axiom 4.1.9 for `H`. -/
theorem HasTitsSystem.basedTransport (hP : P.HasTitsSystem) :
    (P.basedTransport σ f h).HasTitsSystem :=
  hasTitsSystem_of_iso P (P.basedTransport σ f h) (pointsEquiv f)
    (P.map_zeroSubgroup_pointsEquiv σ f h) (P.basedBuildingEquiv σ f h)
    (P.basedBuildingEquiv_smul σ f h) (P.isBuildingIso_basedBuildingEquiv σ f h)
    (P.basedApartmentEquiv σ f h) (P.basedBuildingEquiv_apartmentMap σ f h)
    (P.basedBuildingEquiv_translatedApartmentMap σ f h)
    (P.transportedRoots_basedApartmentEquiv σ f h)
    (mem_normalizerPoints_transport_iff σ f h) hP

end Transport

end ParahoricBuildingData

end Langlands.Geometry.Building
