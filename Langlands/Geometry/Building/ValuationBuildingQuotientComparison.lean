import Langlands.Geometry.Building.ApartmentQuotientComparison
import Langlands.Geometry.Building.AffineFacetTransport
import Langlands.Geometry.Building.FullValidity.Assignment

/-!
# Comparison of the existing valuation-building quotients

All geometric hypotheses are explicit. This module supplies no existence of
valuation data or building axioms for arbitrary connected reductive groups.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- Any two points lie in a common translate of the canonical apartment. -/
abbrev HasCommonApartments : Prop :=
  ApartmentQuotient.HasCommonTranslatedApartment B.apartment.sharpFixerFamily

/-- Every quotient point belongs to a full affine-root facet. -/
theorem exists_isFacet_mem (q : B.ReducedBuilding) :
    ∃ Y, B.IsFacet Y ∧ q ∈ Y := by
  obtain ⟨g, x, rfl⟩ := B.exists_smul_apartmentMap q
  refine ⟨(fun x => g • B.apartmentMap x) '' AffineRootSystem.facet B.affineRoots x,
    ⟨g, _, ⟨x, rfl⟩, rfl⟩, x, ?_, rfl⟩
  exact AffineRootSystem.mem_facet_self _ x

/-- BL 3 and downward closure of apartment subcomplexes give a common geometric
apartment for any two points of a supplied building realization. -/
theorem SatisfiesBuildingAxiom.exists_common_apartment
    {R : B.PolysimplicialRealization} (h : B.SatisfiesBuildingAxiom R)
    (q q' : B.ReducedBuilding) :
    ∃ Y, B.IsApartment Y ∧ q ∈ Y ∧ q' ∈ Y := by
  obtain ⟨Y₁, hY₁, hq⟩ := B.exists_isFacet_mem q
  obtain ⟨Y₂, hY₂, hq'⟩ := B.exists_isFacet_mem q'
  let Fc₁ := R.realize.symm ⟨Y₁, hY₁⟩
  let Fc₂ := R.realize.symm ⟨Y₂, hY₂⟩
  obtain ⟨C, hC, hFC⟩ :=
    h.isBuilding.isChamberComplex.2.1 Fc₁.val Fc₁.property
  obtain ⟨D, hD, hFD⟩ :=
    h.isBuilding.isChamberComplex.2.1 Fc₂.val Fc₂.property
  obtain ⟨𝒜, h𝒜, hC𝒜, hD𝒜⟩ := h.isBuilding.exists_apartment C D hC hD
  have hF₁𝒜 := (h.isBuilding.isSubcomplex 𝒜 h𝒜).2 C hC𝒜 Fc₁.val Fc₁.property hFC
  have hF₂𝒜 := (h.isBuilding.isSubcomplex 𝒜 h𝒜).2 D hD𝒜 Fc₂.val Fc₂.property hFD
  obtain ⟨Y, hY, h𝒜Y⟩ := h𝒜
  rw [h𝒜Y] at hF₁𝒜 hF₂𝒜
  obtain ⟨_, hsub₁⟩ := hF₁𝒜
  obtain ⟨_, hsub₂⟩ := hF₂𝒜
  change (R.realize Fc₁).val ⊆ Y at hsub₁
  change (R.realize Fc₂).val ⊆ Y at hsub₂
  have hY₁Y : Y₁ ⊆ Y := by
    simpa only [Fc₁, Equiv.apply_symm_apply] using hsub₁
  have hY₂Y : Y₂ ⊆ Y := by
    simpa only [Fc₂, Equiv.apply_symm_apply] using hsub₂
  exact ⟨Y, hY, hY₁Y hq, hY₂Y hq'⟩

/-- A supplied witness of KP Axiom 4.1.1 proves the common-apartment hypothesis
used by the quotient comparison. -/
theorem SatisfiesBuildingAxiom.hasCommonApartments
    {R : B.PolysimplicialRealization} (h : B.SatisfiesBuildingAxiom R) :
    B.HasCommonApartments := by
  intro q q'
  obtain ⟨Y, ⟨g, rfl⟩, hq, hq'⟩ := h.exists_common_apartment B q q'
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hq
  obtain ⟨_, ⟨y, rfl⟩, hy⟩ := hq'
  exact ⟨g, x, y, hx, hy⟩

variable (B₁ B₂ : ValuationBuildingData G)
  (e : B₁.Apartment ≃ᵃ[ℝ] B₂.Apartment)
  (hN : ∀ (n : normalizerPoints B₁.i) (x : B₁.Apartment),
    B₂.apartmentMap (e (n • x)) = (n : rationalPoints G) • B₂.apartmentMap (e x))
  (hfix : ∀ x : B₁.Apartment, B₁.sharpFixer {x} ≤ B₂.fixer (B₂.apartmentMap (e x)))

/-- The target apartment map, equivariant for the source normalizer. -/
def comparisonApartmentMap : B₁.Apartment →[normalizerPoints B₁.i] B₂.ReducedBuilding where
  toFun x := B₂.apartmentMap (e x)
  map_smul' := hN

/-- The unique extension to the existing valuation quotient and its existing
rational-points action. The fixer inclusion is required at every source point. -/
def quotientComparison : B₁.ReducedBuilding →[rationalPoints G] B₂.ReducedBuilding :=
  ApartmentQuotient.lift B₁.apartment.sharpFixerFamily
    (comparisonApartmentMap B₁ B₂ e hN) hfix

@[simp]
theorem quotientComparison_apartment (x : B₁.Apartment) :
    quotientComparison B₁ B₂ e hN hfix (B₁.apartmentMap x) = B₂.apartmentMap (e x) :=
  ApartmentQuotient.lift_apartment B₁.apartment.sharpFixerFamily
    (comparisonApartmentMap B₁ B₂ e hN) hfix x

theorem quotientComparison_surjective :
    Function.Surjective (quotientComparison B₁ B₂ e hN hfix) := by
  apply (ApartmentQuotient.lift_surjective_iff B₁.apartment.sharpFixerFamily
    (comparisonApartmentMap B₁ B₂ e hN) hfix).2
  intro q
  obtain ⟨g, x, hx⟩ := B₂.exists_smul_apartmentMap q
  refine ⟨g, e.symm x, ?_⟩
  change g • B₂.apartmentMap (e (e.symm x)) = q
  rwa [e.apply_symm_apply]

theorem quotientComparison_injective (hcommon : B₁.HasCommonApartments)
    (hinj : Function.Injective B₂.apartmentMap) :
    Function.Injective (quotientComparison B₁ B₂ e hN hfix) := by
  apply ApartmentQuotient.lift_injective B₁.apartment.sharpFixerFamily
    (comparisonApartmentMap B₁ B₂ e hN) hfix hcommon
  exact hinj.comp e.injective

/-- An equivalence of the actual valuation quotients, under common source
apartments and injectivity of the target apartment map. -/
def quotientComparisonEquiv (hcommon : B₁.HasCommonApartments)
    (hinj : Function.Injective B₂.apartmentMap) :
    B₁.ReducedBuilding ≃ B₂.ReducedBuilding :=
  Equiv.ofBijective (quotientComparison B₁ B₂ e hN hfix)
    ⟨quotientComparison_injective B₁ B₂ e hN hfix hcommon hinj,
      quotientComparison_surjective B₁ B₂ e hN hfix⟩

section Equivalence

variable (hcommon : B₁.HasCommonApartments) (hinj : Function.Injective B₂.apartmentMap)

local notation "Φ" => quotientComparisonEquiv B₁ B₂ e hN hfix hcommon hinj

@[simp]
theorem quotientComparisonEquiv_apartment (x : B₁.Apartment) :
    Φ (B₁.apartmentMap x) = B₂.apartmentMap (e x) :=
  quotientComparison_apartment B₁ B₂ e hN hfix x

theorem quotientComparisonEquiv_smul (g : rationalPoints G) (q : B₁.ReducedBuilding) :
    Φ (g • q) = g • Φ q :=
  (quotientComparison B₁ B₂ e hN hfix).map_smul g q

theorem quotientComparisonEquiv_symm_smul (g : rationalPoints G) (q : B₂.ReducedBuilding) :
    (Φ).symm (g • q) = g • (Φ).symm q := by
  apply (Φ).injective
  rw [Equiv.apply_symm_apply, quotientComparisonEquiv_smul, Equiv.apply_symm_apply]

theorem quotientComparisonEquiv_translatedApartmentMap
    (g : rationalPoints G) (x : B₁.Apartment) :
    Φ (B₁.translatedApartmentMap g x) = B₂.translatedApartmentMap g (e x) := by
  change Φ (g • B₁.apartmentMap x) = g • B₂.apartmentMap (e x)
  rw [quotientComparisonEquiv_smul, quotientComparisonEquiv_apartment]

/-- Every translated apartment subset is transported using the same group
element and the supplied affine equivalence. -/
theorem quotientComparisonEquiv_image_translatedApartmentMap
    (g : rationalPoints G) (Fa : Set B₁.Apartment) :
    Φ '' (B₁.translatedApartmentMap g '' Fa) =
      B₂.translatedApartmentMap g '' (e '' Fa) := by
  rw [Set.image_image, Set.image_image]
  congr 1
  funext x
  exact quotientComparisonEquiv_translatedApartmentMap B₁ B₂ e hN hfix hcommon hinj g x

theorem quotientComparisonEquiv_image_apartment (g : rationalPoints G) :
    Φ '' (g • B₁.apartmentImage) = g • B₂.apartmentImage := by
  rw [← B₁.range_translatedApartmentMap, ← B₂.range_translatedApartmentMap,
    ← Set.image_univ, quotientComparisonEquiv_image_translatedApartmentMap]
  rw [Set.image_univ_of_surjective e.surjective]
  exact Set.image_univ

theorem quotientComparisonEquiv_isApartment_image_iff (Y : Set B₁.ReducedBuilding) :
    B₂.IsApartment (Φ '' Y) ↔ B₁.IsApartment Y := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, (Φ).injective.image_injective ?_⟩
    rw [quotientComparisonEquiv_image_apartment, hg]
  · rintro ⟨g, rfl⟩
    exact ⟨g, quotientComparisonEquiv_image_apartment B₁ B₂ e hN hfix hcommon hinj g⟩

variable (hroots : AffineRootSystem.transportedRoots e B₁.affineRoots = B₂.affineRoots)

include hroots

/-- Equality of transported full root sets gives preservation and reflection
of full building facets. -/
theorem quotientComparisonEquiv_isFacet_image_iff (Y : Set B₁.ReducedBuilding) :
    B₂.IsFacet (Φ '' Y) ↔ B₁.IsFacet Y := by
  constructor
  · rintro ⟨g, Fa₂, hFa₂, hY⟩
    have himage : e '' (e.symm '' Fa₂) = Fa₂ := e.toEquiv.image_symm_image Fa₂
    have hFa₁ : AffineRootSystem.IsFacet B₁.affineRoots (e.symm '' Fa₂) := by
      apply (AffineRootSystem.isFacet_image_iff_of_transportedRoots_eq e hroots _).1
      rwa [himage]
    refine ⟨g, e.symm '' Fa₂, hFa₁, (Φ).injective.image_injective ?_⟩
    change Φ '' Y = Φ '' (B₁.translatedApartmentMap g '' (e.symm '' Fa₂))
    rw [quotientComparisonEquiv_image_translatedApartmentMap, himage]
    exact hY
  · rintro ⟨g, Fa₁, hFa₁, rfl⟩
    refine ⟨g, e '' Fa₁,
      (AffineRootSystem.isFacet_image_iff_of_transportedRoots_eq e hroots _).2 hFa₁, ?_⟩
    exact quotientComparisonEquiv_image_translatedApartmentMap
      B₁ B₂ e hN hfix hcommon hinj g Fa₁

/-- The comparison is an affine building isomorphism for the Library's actual
facet, apartment and chart predicates. -/
theorem quotientComparisonEquiv_isBuildingIso :
    IsBuildingIso B₁ B₂ Φ where
  isFacet_image_iff :=
    quotientComparisonEquiv_isFacet_image_iff B₁ B₂ e hN hfix hcommon hinj hroots
  isApartment_image_iff :=
    quotientComparisonEquiv_isApartment_image_iff B₁ B₂ e hN hfix hcommon hinj
  exists_affineEquiv g :=
    ⟨g, e, quotientComparisonEquiv_translatedApartmentMap
      B₁ B₂ e hN hfix hcommon hinj g⟩

/-- The building isomorphism uses the identity on actual rational points. -/
theorem quotientComparisonEquiv_isEquivariantBuildingIso :
    IsEquivariantBuildingIso B₁ B₂ (MonoidHom.id _) Φ :=
  ⟨quotientComparisonEquiv_isBuildingIso B₁ B₂ e hN hfix hcommon hinj hroots,
    quotientComparisonEquiv_smul B₁ B₂ e hN hfix hcommon hinj⟩

end Equivalence

end Langlands.Geometry.Building.ValuationBuildingData
