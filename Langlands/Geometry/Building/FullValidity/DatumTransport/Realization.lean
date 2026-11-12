import Langlands.Geometry.Building.FullValidity.DatumTransport.Building
import Langlands.Geometry.Building.ValuationBuildingRealizationTransport
import Langlands.GroupScheme.ConjugacyBaseChange

/-!
# Axiom 4.1.1 under based group isomorphisms

A polysimplicial realization of `B(G)` is carried along a building isomorphism by keeping the
complex and imaging the realized facets. Along the comparison `B(G) ≃ B(H)` of
`ValuationBuildingData.basedTransport`, every clause of `SatisfiesBuildingAxiom` is preserved:
face compatibility and the polysimplicial action follow from the charts of the comparison, the
apartments of the complex are unchanged, and the torus–apartment correspondence and the
normalizer stabilizer are carried by `f`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

open DatumTransport

/-- An affine equivalence maps the image under its inverse back. -/
theorem DatumTransport.affineEquiv_image_symm_image {V₁ V₂ P₁ P₂ : Type*} [AddCommGroup V₁]
    [Module ℝ V₁] [AddTorsor V₁ P₁] [AddCommGroup V₂] [Module ℝ V₂] [AddTorsor V₂ P₂]
    (A : P₁ ≃ᵃ[ℝ] P₂) (s : Set P₂) : A '' (A.symm '' s) = s :=
  A.toEquiv.image_symm_image s

namespace ValuationBuildingData

/-! ### Realizations along building isomorphisms -/

section Charts

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G₁ G₂ : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G₁.X.hom]
  [IsAffineHom G₂.X.hom]
  {B₁ : ValuationBuildingData G₁} {B₂ : ValuationBuildingData G₂}
  (Φ : B₁.ReducedBuilding ≃ B₂.ReducedBuilding) (hiso : IsBuildingIso B₁ B₂ Φ)

/-- The facets of `B(G₁)` and `B(G₂)` correspond under a building isomorphism. -/
def facetEquivOfIsBuildingIso : BuildingFacet B₁ ≃ BuildingFacet B₂ :=
  Φ.setCongr.subtypeEquiv fun Y => (hiso.isFacet_image_iff Y).symm

@[simp] theorem facetEquivOfIsBuildingIso_val (Fc : BuildingFacet B₁) :
    (facetEquivOfIsBuildingIso Φ hiso Fc).val = Φ '' Fc.val := rfl

/-- The realization carried along a building isomorphism: the same complex, with realized
facets imaged by `Φ`. -/
def PolysimplicialRealization.mapBuildingIso (R : B₁.PolysimplicialRealization) :
    B₂.PolysimplicialRealization where
  index := R.index
  V := R.V
  complex := R.complex
  realize := R.realize.trans (facetEquivOfIsBuildingIso Φ hiso)

@[simp] theorem PolysimplicialRealization.mapBuildingIso_realize
    (R : B₁.PolysimplicialRealization) (Fc : R.complex.facets) :
    ((R.mapBuildingIso Φ hiso).realize Fc).val = Φ '' (R.realize Fc).val := rfl

theorem PolysimplicialRealization.mapBuildingIso_apartmentComplex_image
    (R : B₁.PolysimplicialRealization) (Y : Set B₁.ReducedBuilding) :
    (R.mapBuildingIso Φ hiso).apartmentComplex (Φ '' Y) = R.apartmentComplex Y := by
  ext Fc
  constructor
  · rintro ⟨h, hsub⟩
    refine ⟨h, ?_⟩
    change Φ '' (R.realize ⟨Fc, h⟩).val ⊆ Φ '' Y at hsub
    exact (Set.image_subset_image_iff Φ.injective).1 hsub
  · rintro ⟨h, hsub⟩
    exact ⟨h, Set.image_mono hsub⟩

/-- The apartments of the complex are unchanged. -/
theorem PolysimplicialRealization.mapBuildingIso_apartments
    (R : B₁.PolysimplicialRealization) :
    (R.mapBuildingIso Φ hiso).apartments = R.apartments := by
  ext 𝒜
  constructor
  · rintro ⟨Y, hY, h𝒜⟩
    have hY' : B₁.IsApartment (Φ.symm '' Y) :=
      (hiso.isApartment_image_iff _).1 (by simpa only [Φ.image_symm_image] using hY)
    refine ⟨Φ.symm '' Y, hY', ?_⟩
    rw [h𝒜, ← R.mapBuildingIso_apartmentComplex_image Φ hiso, Φ.image_symm_image]
  · rintro ⟨Y, hY, h𝒜⟩
    exact ⟨Φ '' Y, (hiso.isApartment_image_iff Y).2 hY,
      h𝒜.trans (R.mapBuildingIso_apartmentComplex_image Φ hiso Y).symm⟩

/-- `K` with its apartments is a building for the carried realization. -/
theorem PolysimplicialRealization.mapBuildingIso_isBuilding (R : B₁.PolysimplicialRealization)
    (hR : AbstractBuilding.IsBuilding R.complex R.apartments) :
    AbstractBuilding.IsBuilding (R.mapBuildingIso Φ hiso).complex
      (R.mapBuildingIso Φ hiso).apartments := by
  rw [R.mapBuildingIso_apartments Φ hiso]
  exact hR

section Equivariant

variable (φ : rationalPoints G₁ ≃* rationalPoints G₂)
  (hsmul : ∀ (g : rationalPoints G₁) (y : B₁.ReducedBuilding), Φ (g • y) = φ g • Φ y)

include hsmul in
theorem image_smul_of_equivariant (g : rationalPoints G₁) (Y : Set B₁.ReducedBuilding) :
    Φ '' (g • Y) = φ g • (Φ '' Y) := by
  change Φ '' ((fun q => g • q) '' Y) = (fun q => φ g • q) '' (Φ '' Y)
  rw [Set.image_image, Set.image_image]
  exact Set.image_congr fun q _ => hsmul g q

include hsmul in
/-- The polysimplicial action is carried along an equivariant building isomorphism. -/
theorem PolysimplicialRealization.mapBuildingIso_isPolysimplicialAction
    (R : B₁.PolysimplicialRealization) (hR : R.IsPolysimplicialAction) :
    (R.mapBuildingIso Φ hiso).IsPolysimplicialAction := by
  intro g
  obtain ⟨e, he, heg⟩ := hR (φ.symm g)
  refine ⟨e, he, fun Fc Fc' => ?_⟩
  change Fc'.val = e '' Fc.val ↔
    Φ '' (R.realize Fc').val = (fun q => g • q) '' (Φ '' (R.realize Fc).val)
  refine (heg Fc Fc').trans ?_
  change (R.realize Fc').val = φ.symm g • (R.realize Fc).val ↔
    Φ '' (R.realize Fc').val = g • (Φ '' (R.realize Fc).val)
  rw [← MulEquiv.apply_symm_apply φ g, ← image_smul_of_equivariant Φ φ hsmul,
    MulEquiv.symm_apply_apply]
  exact Φ.injective.image_injective.eq_iff.symm

end Equivariant

section FaceRelation

variable (φ : rationalPoints G₁ ≃* rationalPoints G₂) (A : B₁.Apartment ≃ᵃ[ℝ] B₂.Apartment)
  (hΦ : ∀ g x, Φ (B₁.translatedApartmentMap g x) = B₂.translatedApartmentMap (φ g) (A x))
  (hroots : AffineRootSystem.transportedRoots A B₁.affineRoots = B₂.affineRoots)

include hΦ hroots in
/-- The face relation of building facets is preserved and reflected. -/
theorem facetPrecedes_facetEquiv_iff_of_chart (Fc Fc' : BuildingFacet B₁) :
    FacetPrecedes B₂ (facetEquivOfIsBuildingIso Φ hiso Fc)
        (facetEquivOfIsBuildingIso Φ hiso Fc') ↔ FacetPrecedes B₁ Fc Fc' := by
  constructor
  · rintro ⟨g, Fb, Fb', hface, hFb, hFb'⟩
    have hface' : AffineRootSystem.IsFaceOf B₁.affineRoots (A.symm '' Fb) (A.symm '' Fb') := by
      apply (AffineRootSystem.isFaceOf_image_transportedRoots_iff A _ _ _).1
      rwa [hroots, affineEquiv_image_symm_image, affineEquiv_image_symm_image]
    refine ⟨φ.symm g, A.symm '' Fb, A.symm '' Fb', hface', ?_, ?_⟩
    · apply Φ.injective.image_injective
      rw [image_translatedApartmentMap_of_chart Φ φ A hΦ, MulEquiv.apply_symm_apply,
        affineEquiv_image_symm_image]
      exact hFb
    · apply Φ.injective.image_injective
      rw [image_translatedApartmentMap_of_chart Φ φ A hΦ, MulEquiv.apply_symm_apply,
        affineEquiv_image_symm_image]
      exact hFb'
  · rintro ⟨g, Fa, Fa', hface, hFa, hFa'⟩
    refine ⟨φ g, A '' Fa, A '' Fa', ?_, ?_, ?_⟩
    · rw [← hroots]
      exact (AffineRootSystem.isFaceOf_image_transportedRoots_iff A _ _ _).2 hface
    · change Φ '' Fc.val = _
      rw [hFa, image_translatedApartmentMap_of_chart Φ φ A hΦ]
    · change Φ '' Fc'.val = _
      rw [hFa', image_translatedApartmentMap_of_chart Φ φ A hΦ]

include hΦ hroots in
/-- Face compatibility is carried along a chart-compatible building isomorphism. -/
theorem PolysimplicialRealization.mapBuildingIso_isFaceCompatible
    (R : B₁.PolysimplicialRealization) (hR : R.IsFaceCompatible) :
    (R.mapBuildingIso Φ hiso).IsFaceCompatible := fun Fc Fc' =>
  (hR Fc Fc').trans
    (facetPrecedes_facetEquiv_iff_of_chart Φ hiso φ A hΦ hroots (R.realize Fc)
      (R.realize Fc')).symm

end FaceRelation

end Charts

/-! ### Tori and apartments along `f` -/

section Transport

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (B : ValuationBuildingData G) {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {j : S.toGrp ⟶ H} (σ : B.S ≅ S) (f : G ≅ H)
  (h : B.i ≫ f.hom = CommGroupScheme.groupHom σ.hom ≫ j)

/-- The canonical apartment of `B(G)` is carried onto that of `B(H)`. -/
theorem image_apartmentImage_basedBuildingEquiv :
    B.basedBuildingEquiv σ f h '' B.apartmentImage =
      (B.basedTransport σ f h).apartmentImage := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨B.basedApartmentEquiv σ f h x, (B.basedBuildingEquiv_apartmentMap σ f h x).symm⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := (B.basedApartmentEquiv σ f h).surjective x
    exact ⟨B.apartmentMap x, ⟨x, rfl⟩, B.basedBuildingEquiv_apartmentMap σ f h x⟩

omit [IsAffineHom H.X.hom] in
include h in
/-- Conjugation by `f(g)` on the target torus is conjugation by `g` on `S`, carried by `σ` and
`f`. -/
theorem innerIso_basedTransport (g : rationalPoints G) :
    j ≫ (H.innerIso (rationalPoints.map f.hom g)).hom =
      CommGroupScheme.groupHom σ.inv ≫ (B.i ≫ (G.innerIso g).hom) ≫ f.hom := by
  rw [target_eq σ f h]
  simp only [Category.assoc]
  rw [innerIso_hom_comp]
  rfl

include h in
/-- The conjugate torus `f(g) S' f(g)⁻¹` of `H` is the image of `g S g⁻¹` under `f`. -/
theorem conjTorus_basedTransport (g : rationalPoints G) :
    (B.basedTransport σ f h).conjTorus (rationalPoints.map f.hom g) =
      SubgroupFunctor.range ((B.i ≫ (G.innerIso g).hom) ≫ f.hom) := by
  refine (congrArg SubgroupFunctor.range (innerIso_basedTransport B σ f h g)).trans ?_
  exact SubgroupFunctor.range_iso_comp (torusGrpIso σ).symm _

include h in
theorem conjTorus_basedTransport_eq_iff (g g' : rationalPoints G) :
    (B.basedTransport σ f h).conjTorus (rationalPoints.map f.hom g) =
        (B.basedTransport σ f h).conjTorus (rationalPoints.map f.hom g') ↔
      B.conjTorus g = B.conjTorus g' := by
  rw [conjTorus_basedTransport, conjTorus_basedTransport]
  constructor
  · intro heq
    have h₁ := SubgroupFunctor.range_comp_mono heq.le f.inv
    have h₂ := SubgroupFunctor.range_comp_mono heq.ge f.inv
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h₁ h₂
    exact le_antisymm h₁ h₂
  · intro heq
    exact le_antisymm (SubgroupFunctor.range_comp_mono heq.le f.hom)
      (SubgroupFunctor.range_comp_mono heq.ge f.hom)

/-- The torus–apartment correspondence of Axiom 4.1.1 is carried along `f`. -/
theorem HasTorusApartmentCorrespondence.basedTransport
    (hB : B.HasTorusApartmentCorrespondence) :
    (B.basedTransport σ f h).HasTorusApartmentCorrespondence where
  exists_torusChart T₂ i₂ hi₂ := by
    obtain ⟨g, τ, hτ⟩ := hB.exists_torusChart T₂ (i₂ ≫ f.inv) (hi₂.comp_iso f.symm)
    refine ⟨rationalPoints.map f.hom g, σ.symm ≪≫ τ, ?_⟩
    have hτ' : B.i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom τ.hom ≫ i₂ ≫ f.inv := hτ
    change j ≫ (H.innerIso (rationalPoints.map f.hom g)).hom =
      CommGroupScheme.groupHom σ.inv ≫ CommGroupScheme.groupHom τ.hom ≫ i₂
    rw [innerIso_basedTransport B σ f h g, hτ']
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  conjTorus_eq_iff g g' := by
    obtain ⟨g, rfl⟩ := (pointsEquiv f).surjective g
    obtain ⟨g', rfl⟩ := (pointsEquiv f).surjective g'
    rw [← image_apartmentImage_basedBuildingEquiv B σ f h,
      ← image_smul_of_equivariant _ (pointsEquiv f) (B.basedBuildingEquiv_smul σ f h),
      ← image_smul_of_equivariant _ (pointsEquiv f) (B.basedBuildingEquiv_smul σ f h),
      (B.basedBuildingEquiv σ f h).injective.image_injective.eq_iff, ← hB.conjTorus_eq_iff,
      pointsEquiv_apply, pointsEquiv_apply]
    exact conjTorus_basedTransport_eq_iff B σ f h g g'

/-- The stabilizer clause of Axiom 4.1.1 is carried along `f`. -/
theorem HasNormalizerApartmentStabilizer.basedTransport
    (hB : B.HasNormalizerApartmentStabilizer) :
    (B.basedTransport σ f h).HasNormalizerApartmentStabilizer := by
  apply (B.basedTransport σ f h).hasNormalizerApartmentStabilizer_iff.2
  intro g hg
  obtain ⟨g, rfl⟩ := (pointsEquiv f).surjective g
  change g ≫ f.hom.hom.hom ∈ normalizerPoints j
  rw [mem_normalizerPoints_transport_iff σ f h]
  apply (B.hasNormalizerApartmentStabilizer_iff.1 hB) g
  apply (B.basedBuildingEquiv σ f h).injective.image_injective
  rw [image_smul_of_equivariant _ (pointsEquiv f) (B.basedBuildingEquiv_smul σ f h),
    image_apartmentImage_basedBuildingEquiv]
  exact hg

/-- The realization of `B(H)`: the same polysimplicial complex, realized through the
comparison of reduced buildings. -/
def PolysimplicialRealization.basedTransport (R : B.PolysimplicialRealization) :
    (B.basedTransport σ f h).PolysimplicialRealization :=
  R.mapBuildingIso _ (B.isBuildingIso_basedBuildingEquiv σ f h)

/-- Axiom 4.1.1 for `G` gives Axiom 4.1.1 for `H` with the transported data. -/
theorem SatisfiesBuildingAxiom.basedTransport {R : B.PolysimplicialRealization}
    (hR : B.SatisfiesBuildingAxiom R) :
    (B.basedTransport σ f h).SatisfiesBuildingAxiom (R.basedTransport B σ f h) where
  faceCompatible := R.mapBuildingIso_isFaceCompatible _ _ (pointsEquiv f) _
    (B.basedBuildingEquiv_translatedApartmentMap σ f h)
    (B.transportedRoots_basedApartmentEquiv σ f h) hR.faceCompatible
  isBuilding := R.mapBuildingIso_isBuilding _ _ hR.isBuilding
  polysimplicialAction := R.mapBuildingIso_isPolysimplicialAction _ _ (pointsEquiv f)
    (B.basedBuildingEquiv_smul σ f h) hR.polysimplicialAction
  torusApartmentCorrespondence := hR.torusApartmentCorrespondence.basedTransport B σ f h
  normalizerApartmentStabilizer := hR.normalizerApartmentStabilizer.basedTransport B σ f h

end Transport

end ValuationBuildingData

end Langlands.Geometry.Building
