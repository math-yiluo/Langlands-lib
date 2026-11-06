import Langlands.Geometry.Building.BuildingFacetAction
import Langlands.Geometry.Building.FullValidity.Realization
import Langlands.Geometry.Building.TitsFacetApartmentTransport

/-! # Apartment order isomorphisms on a supplied face-compatible realization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

namespace ValuationBuildingData.PolysimplicialRealization

variable {B : ValuationBuildingData G} (R : B.PolysimplicialRealization)

/-- Pull the original facet permutation back through a face-compatible realization. -/
def facetTranslateOrderIso (hR : R.IsFaceCompatible) (g : rationalPoints G) :
    R.complex.facets ≃o R.complex.facets where
  toEquiv := (R.realize.trans (B.facetTranslateEquiv g)).trans R.realize.symm
  map_rel_iff' := by
    intro Fc Fd
    change (R.realize.symm (B.facetTranslateEquiv g (R.realize Fc))).val ⊆
      (R.realize.symm (B.facetTranslateEquiv g (R.realize Fd))).val ↔ Fc.val ⊆ Fd.val
    rw [hR, hR]
    simp only [Equiv.apply_symm_apply, B.facetPrecedes_translate_iff]

@[simp] theorem realize_facetTranslateOrderIso
    (hR : R.IsFaceCompatible) (g : rationalPoints G) (Fc : R.complex.facets) :
    R.realize (R.facetTranslateOrderIso hR g Fc) = B.facetTranslateEquiv g (R.realize Fc) :=
  R.realize.apply_symm_apply _

/-- Regard an apartment's facets as complex facets with the stated containment. -/
def apartmentFacetOrderIso (Y : Set B.ReducedBuilding) :
    R.apartmentComplex Y ≃o {Fc : R.complex.facets // (R.realize Fc).val ⊆ Y} where
  toFun Fc := ⟨⟨Fc.val, Fc.property.choose⟩, Fc.property.choose_spec⟩
  invFun Fc := ⟨Fc.val.val, ⟨Fc.val.property, Fc.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- The complex facet underlying a member of an apartment complex. -/
def apartmentFacet (Y : Set B.ReducedBuilding) (Fc : R.apartmentComplex Y) :
    R.complex.facets := (R.apartmentFacetOrderIso Y Fc).val

@[simp] theorem apartmentFacet_val (Y : Set B.ReducedBuilding)
    (Fc : R.apartmentComplex Y) : (R.apartmentFacet Y Fc).val = Fc.val := rfl

theorem apartmentFacet_subset (Y : Set B.ReducedBuilding) (Fc : R.apartmentComplex Y) :
    (R.realize (R.apartmentFacet Y Fc)).val ⊆ Y :=
  (R.apartmentFacetOrderIso Y Fc).property

/-- Translation restricts to an order isomorphism of the realized apartment complexes. -/
def apartmentTranslateOrderIso (hR : R.IsFaceCompatible) (g : rationalPoints G)
    (Y Z : Set B.ReducedBuilding) (hg : g • Y = Z) :
    R.apartmentComplex Y ≃o R.apartmentComplex Z := by
  let e := R.facetTranslateOrderIso hR g
  let e' : {Fc : R.complex.facets // (R.realize Fc).val ⊆ Y} ≃o
      {Fc : R.complex.facets // (R.realize Fc).val ⊆ Z} :=
    { toEquiv := e.toEquiv.subtypeEquiv (by
        intro Fc
        change (R.realize Fc).val ⊆ Y ↔ (R.realize (e Fc)).val ⊆ Z
        rw [R.realize_facetTranslateOrderIso, B.facetTranslateEquiv_val, ← hg]
        exact Set.smul_set_subset_smul_set_iff.symm)
      map_rel_iff' := by
        intro Fc Fd
        change e Fc.val ≤ e Fd.val ↔ Fc.val ≤ Fd.val
        exact e.map_rel_iff }
  exact (R.apartmentFacetOrderIso Y).trans (e'.trans (R.apartmentFacetOrderIso Z).symm)

theorem realize_apartmentTranslateOrderIso
    (hR : R.IsFaceCompatible) (g : rationalPoints G)
    (Y Z : Set B.ReducedBuilding) (hg : g • Y = Z) (Fc : R.apartmentComplex Y) :
    R.realize (R.apartmentFacet Z (R.apartmentTranslateOrderIso hR g Y Z hg Fc)) =
      B.facetTranslateEquiv g (R.realize (R.apartmentFacet Y Fc)) :=
  R.realize_facetTranslateOrderIso hR g _

/-- Face compatibility and apartment incidence make each apartment a subcomplex. -/
theorem isSubcomplex_apartmentComplex (hR : R.IsFaceCompatible)
    (hD : B.SatisfiesApartmentAxioms) {Y : Set B.ReducedBuilding}
    (hY : B.IsApartment Y) :
    AbstractBuilding.IsSubcomplex (R.apartmentComplex Y) R.complex.facets := by
  refine ⟨fun _ h => h.choose, ?_⟩
  rintro A ⟨hA, hAY⟩ C hC hCA
  obtain ⟨g, rfl⟩ := hY
  refine ⟨hC, B.subset_apartment_of_facetPrecedes hD
    ((hR ⟨C, hC⟩ ⟨A, hA⟩).mp hCA) g hAY⟩

end ValuationBuildingData.PolysimplicialRealization

namespace ParahoricBuildingData

variable {P : ParahoricBuildingData G}
  {Ca : Set P.Apartment} {W : Type u} [Group W]
  {π : P.normalizerInZero →* W} {Sgen : Set W}

/-- One Tits-system transporter fixes every subface of either common facet. -/
theorem IsBuildingTitsSystem.exists_realization_apartmentOrderIso
    (hT : P.IsBuildingTitsSystem Ca π Sgen)
    (R : P.toValuationBuildingData.PolysimplicialRealization) (hR : R.IsFaceCompatible)
    {Y Z : Set P.ReducedBuilding} (hY : P.IsApartment Y) (hZ : P.IsApartment Z)
    (F₁ F₂ : R.complex.facets)
    (hF₁Y : (R.realize F₁).val ⊆ Y) (hF₂Y : (R.realize F₂).val ⊆ Y)
    (hF₁Z : (R.realize F₁).val ⊆ Z) (hF₂Z : (R.realize F₂).val ⊆ Z) :
    ∃ φ : R.apartmentComplex Y ≃o R.apartmentComplex Z,
      ∀ (Fc : Set (∀ i, R.V i)) (hFc : Fc ∈ R.apartmentComplex Y),
        (Fc ⊆ F₁.val ∨ Fc ⊆ F₂.val) →
          (φ ⟨Fc, hFc⟩).val = Fc := by
  obtain ⟨k, hk₁, hk₂, hkYZ⟩ := hT.exists_twoFacet_smul_apartment_eq hY hZ
    (R.realize F₁) (R.realize F₂) hF₁Y hF₂Y hF₁Z hF₂Z
  let φ := R.apartmentTranslateOrderIso hR (k : rationalPoints G) Y Z hkYZ
  refine ⟨φ, ?_⟩
  intro Fc hFc hface
  let Fd := R.apartmentFacet Y ⟨Fc, hFc⟩
  have hk : k ∈ P.facetZeroStabilizer (R.realize Fd) := by
    rcases hface with h | h
    · exact ((hT.facetPrecedes_iff _ _).mp ((hR Fd F₁).mp h)) hk₁
    · exact ((hT.facetPrecedes_iff _ _).mp ((hR Fd F₂).mp h)) hk₂
  have hfix : P.toValuationBuildingData.facetTranslateEquiv k (R.realize Fd) =
      R.realize Fd := by
    apply Subtype.ext
    exact (P.mem_zeroStabilizerIn).mp hk
  have H : R.apartmentFacet Z (φ ⟨Fc, hFc⟩) = Fd := by
    apply R.realize.injective
    exact (R.realize_apartmentTranslateOrderIso hR k Y Z hkYZ ⟨Fc, hFc⟩).trans hfix
  exact congrArg Subtype.val H

/-- BL4 in the exact apartment-family form required by `AbstractBuilding.IsBuilding`. -/
theorem IsBuildingTitsSystem.realization_exists_orderIso
    (hT : P.IsBuildingTitsSystem Ca π Sgen)
    (R : P.toValuationBuildingData.PolysimplicialRealization) (hR : R.IsFaceCompatible) :
    ∀ 𝒜₁ ∈ R.apartments, ∀ 𝒜₂ ∈ R.apartments,
      ∀ F₁ ∈ 𝒜₁ ∩ 𝒜₂, ∀ F₂ ∈ 𝒜₁ ∩ 𝒜₂,
        ∃ φ : 𝒜₁ ≃o 𝒜₂,
          ∀ (Fc : Set (∀ i, R.V i)) (hFc : Fc ∈ 𝒜₁),
            (Fc ⊆ F₁ ∨ Fc ⊆ F₂) → (φ ⟨Fc, hFc⟩).val = Fc := by
  rintro _ ⟨Y, hY, rfl⟩ _ ⟨Z, hZ, rfl⟩ F₁ ⟨hF₁Y, hF₁Z⟩ F₂ ⟨hF₂Y, hF₂Z⟩
  obtain ⟨h₁, h₁Y⟩ := hF₁Y
  obtain ⟨_, h₁Z⟩ := hF₁Z
  obtain ⟨h₂, h₂Y⟩ := hF₂Y
  obtain ⟨_, h₂Z⟩ := hF₂Z
  exact hT.exists_realization_apartmentOrderIso R hR hY hZ
    ⟨F₁, h₁⟩ ⟨F₂, h₂⟩ h₁Y h₂Y h₁Z h₂Z

end ParahoricBuildingData
end Langlands.Geometry.Building
