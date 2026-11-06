import Langlands.Geometry.Building.ValuationBuildingAxiomTransport
import Langlands.GroupScheme.Rational.CrossTorusWeylTransport

/-! # Transport of polysimplicial realizations on actual valuation quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

namespace AffineRootSystem

variable {V A W D : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  [AddCommGroup W] [Module ℝ W] [AddTorsor W D]

/-- Full root transport preserves and reflects the affine-root face relation. -/
theorem isFaceOf_image_transportedRoots_iff (e : A ≃ᵃ[ℝ] D)
    (Ψ : Set (A →ᵃ[ℝ] ℝ)) (Fa Fa' : Set A) :
    IsFaceOf (transportedRoots e Ψ) (e '' Fa) (e '' Fa') ↔ IsFaceOf Ψ Fa Fa' := by
  constructor
  · rintro ⟨hFa, y, hy, hsub⟩
    refine ⟨(isFacet_image_transportedRoots_iff e Ψ Fa).1 hFa, e.symm y, ?_, ?_⟩
    · apply e.injective.image_injective
      rw [image_facet_transportedRoots, e.apply_symm_apply, hy]
    · apply (Set.image_subset_image_iff e.injective).1
      rw [image_facetClosure_transportedRoots, e.apply_symm_apply]
      exact hsub
  · rintro ⟨hFa, x, hx, hsub⟩
    refine ⟨(isFacet_image_transportedRoots_iff e Ψ Fa).2 hFa, e x, ?_, ?_⟩
    · rw [← image_facet_transportedRoots, hx]
    · rw [← image_facetClosure_transportedRoots]
      exact Set.image_mono hsub

end AffineRootSystem

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B₁ B₂ : ValuationBuildingData G)
  (Φ : B₁.ReducedBuilding ≃ B₂.ReducedBuilding)
  (hiso : IsBuildingIso B₁ B₂ Φ)

/-- Retain the source polysimplicial complex and image its realized facets. -/
def PolysimplicialRealization.transport (R : B₁.PolysimplicialRealization) :
    B₂.PolysimplicialRealization where
  index := R.index
  V := R.V
  complex := R.complex
  realize := R.realize.trans (hiso.facetEquiv B₁ B₂ Φ)

@[simp] theorem PolysimplicialRealization.transport_realize
    (R : B₁.PolysimplicialRealization) (Fc : R.complex.facets) :
    ((R.transport B₁ B₂ Φ hiso).realize Fc).val = Φ '' (R.realize Fc).val := rfl

theorem PolysimplicialRealization.transport_apartmentComplex_image
    (R : B₁.PolysimplicialRealization) (Y : Set B₁.ReducedBuilding) :
    (R.transport B₁ B₂ Φ hiso).apartmentComplex (Φ '' Y) = R.apartmentComplex Y := by
  ext Fc
  constructor
  · rintro ⟨h, hsub⟩
    refine ⟨h, ?_⟩
    change Φ '' (R.realize ⟨Fc, h⟩).val ⊆ Φ '' Y at hsub
    exact (Set.image_subset_image_iff Φ.injective).1 hsub
  · rintro ⟨h, hsub⟩
    exact ⟨h, Set.image_mono hsub⟩

theorem PolysimplicialRealization.transport_apartments
    (R : B₁.PolysimplicialRealization) :
    (R.transport B₁ B₂ Φ hiso).apartments = R.apartments := by
  ext 𝒜
  constructor
  · rintro ⟨Y, hY, h𝒜⟩
    have hY' : B₁.IsApartment (Φ.symm '' Y) :=
      (hiso.isApartment_image_iff _).1 (by simpa only [Φ.image_symm_image] using hY)
    refine ⟨Φ.symm '' Y, hY', ?_⟩
    rw [h𝒜, ← R.transport_apartmentComplex_image B₁ B₂ Φ hiso, Φ.image_symm_image]
  · rintro ⟨Y, hY, h𝒜⟩
    exact ⟨Φ '' Y, (hiso.isApartment_image_iff Y).2 hY,
      h𝒜.trans (R.transport_apartmentComplex_image B₁ B₂ Φ hiso Y).symm⟩

section Tori

variable (σ : B₁.S ≅ B₂.S)
  (hσ : B₁.i = CommGroupScheme.groupHom σ.hom ≫ B₂.i)

include hσ

/-- An isomorphism of the actual embedded tori identifies their normalizers
inside the same rational-point group. -/
theorem normalizerPoints_eq_of_torusIso :
    normalizerPoints B₁.i = normalizerPoints B₂.i := by
  ext n
  have hs : B₁.i ≫ (Iso.refl G).hom = CommGroupScheme.groupHom σ.hom ≫ B₂.i := by
    simpa only [Iso.refl_hom, Category.comp_id] using hσ
  have hn := mem_normalizerPoints_transport_iff σ (Iso.refl G) hs n
  simpa only [Iso.refl_hom, Grp.id_hom_hom, Category.comp_id] using hn.symm

/-- The corresponding conjugate tori have equal actual subgroup functors. -/
theorem conjTorus_eq_of_torusIso (g : rationalPoints G) :
    B₁.conjTorus g = B₂.conjTorus g := by
  let eσ : B₁.S.toGrp ≅ B₂.S.toGrp :=
    { hom := CommGroupScheme.groupHom σ.hom
      inv := CommGroupScheme.groupHom σ.inv
      hom_inv_id := congrArg Additive.toMul σ.hom_inv_id
      inv_hom_id := congrArg Additive.toMul σ.inv_hom_id }
  rw [conjTorus, conjTorus, hσ, Category.assoc]
  exact SubgroupFunctor.range_iso_comp eσ (B₂.i ≫ (G.innerIso g).hom)

/-- Transfer an actual torus chart by composing its torus isomorphism. -/
theorem isTorusChart_of_torusIso
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {j : T.toGrp ⟶ G}
    {g : rationalPoints G} {τ : B₁.S ≅ T} (hτ : B₁.IsTorusChart j g τ) :
    B₂.IsTorusChart j g (σ.symm ≪≫ τ) := by
  have hs : B₁.i ≫ (Iso.refl G).hom = CommGroupScheme.groupHom σ.hom ≫ B₂.i := by
    simpa only [Iso.refl_hom, Category.comp_id] using hσ
  have hi : B₂.i = CommGroupScheme.groupHom σ.inv ≫ B₁.i := by
    simpa only [Iso.refl_inv, Category.comp_id] using
      torusTransport_inverse_square σ (Iso.refl G) hs
  change B₁.i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom τ.hom ≫ j at hτ
  change B₂.i ≫ (G.innerIso g).hom = _
  rw [hi, Category.assoc, hτ, ← Category.assoc]
  rfl

end Tori

variable (hΦ : ∀ (g : rationalPoints G) (q : B₁.ReducedBuilding), Φ (g • q) = g • Φ q)

include hΦ

theorem image_smul_of_equivariantEquiv (g : rationalPoints G) (Y : Set B₁.ReducedBuilding) :
    Φ '' (g • Y) = g • (Φ '' Y) := by
  change Φ '' ((fun q => g • q) '' Y) = (fun q => g • q) '' (Φ '' Y)
  rw [Set.image_image, Set.image_image]
  congr 1
  funext q
  exact hΦ g q

theorem PolysimplicialRealization.transport_isPolysimplicialAction
    (R : B₁.PolysimplicialRealization) (hR : R.IsPolysimplicialAction) :
    (R.transport B₁ B₂ Φ hiso).IsPolysimplicialAction := by
  intro g
  obtain ⟨f, hf, hfg⟩ := hR g
  refine ⟨f, hf, fun Fc Fc' => ?_⟩
  change Fc'.val = f '' Fc.val ↔
    Φ '' (R.realize Fc').val = (fun q => g • q) '' (Φ '' (R.realize Fc).val)
  refine (hfg Fc Fc').trans ?_
  change (R.realize Fc').val = g • (R.realize Fc).val ↔
    Φ '' (R.realize Fc').val = g • (Φ '' (R.realize Fc).val)
  rw [← image_smul_of_equivariantEquiv B₁ B₂ Φ hΦ]
  exact Φ.injective.image_injective.eq_iff.symm

variable (e : B₁.Apartment ≃ᵃ[ℝ] B₂.Apartment)
  (hmap : ∀ x : B₁.Apartment, Φ (B₁.apartmentMap x) = B₂.apartmentMap (e x))
  (hroots : AffineRootSystem.transportedRoots e B₁.affineRoots = B₂.affineRoots)

include e hmap

theorem image_translatedApartmentMap_of_comparison (g : rationalPoints G)
    (Fa : Set B₁.Apartment) :
    Φ '' (B₁.translatedApartmentMap g '' Fa) =
      B₂.translatedApartmentMap g '' (e '' Fa) := by
  rw [Set.image_image, Set.image_image]
  congr 1
  funext x
  exact (hΦ g (B₁.apartmentMap x)).trans (congrArg (fun q => g • q) (hmap x))

omit hΦ in
/-- The compatible affine equivalence identifies the canonical apartments. -/
theorem image_apartmentImage_of_comparison :
    Φ '' B₁.apartmentImage = B₂.apartmentImage := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨e x, (hmap x).symm⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨B₁.apartmentMap (e.symm x), ⟨_, rfl⟩, by rw [hmap, e.apply_symm_apply]⟩

section TorusApartments

variable (σ : B₁.S ≅ B₂.S)
  (hσ : B₁.i = CommGroupScheme.groupHom σ.hom ≫ B₂.i)

include hσ

/-- Transfer both clauses of the actual torus/apartment correspondence. -/
theorem hasTorusApartmentCorrespondence_of_comparison
    (hB : B₁.HasTorusApartmentCorrespondence) : B₂.HasTorusApartmentCorrespondence where
  exists_torusChart T j hj := by
    obtain ⟨g, τ, hτ⟩ := hB.exists_torusChart T j hj
    exact ⟨g, σ.symm ≪≫ τ, isTorusChart_of_torusIso B₁ B₂ σ hσ hτ⟩
  conjTorus_eq_iff g h := by
    rw [← conjTorus_eq_of_torusIso B₁ B₂ σ hσ g,
      ← conjTorus_eq_of_torusIso B₁ B₂ σ hσ h]
    refine (hB.conjTorus_eq_iff g h).trans ?_
    rw [← image_apartmentImage_of_comparison B₁ B₂ Φ e hmap,
      ← image_smul_of_equivariantEquiv B₁ B₂ Φ hΦ,
      ← image_smul_of_equivariantEquiv B₁ B₂ Φ hΦ]
    exact Φ.injective.image_injective.eq_iff.symm

/-- Transfer the exact normalizer stabilizer clause for the canonical apartment. -/
theorem hasNormalizerApartmentStabilizer_of_comparison
    (hB : B₁.HasNormalizerApartmentStabilizer) : B₂.HasNormalizerApartmentStabilizer := by
  apply B₂.hasNormalizerApartmentStabilizer_iff.2
  intro g hg
  rw [← normalizerPoints_eq_of_torusIso B₁ B₂ σ hσ]
  apply (HasNormalizerApartmentStabilizer.smul_apartmentImage_eq_iff B₁ hB g).1
  apply Φ.injective.image_injective
  rw [image_smul_of_equivariantEquiv B₁ B₂ Φ hΦ,
    image_apartmentImage_of_comparison B₁ B₂ Φ e hmap, hg]

end TorusApartments

include hroots

theorem facetPrecedes_facetEquiv_iff (Fc Fc' : BuildingFacet B₁) :
    FacetPrecedes B₂ (hiso.facetEquiv B₁ B₂ Φ Fc) (hiso.facetEquiv B₁ B₂ Φ Fc') ↔
      FacetPrecedes B₁ Fc Fc' := by
  have heimage (Y : Set B₂.Apartment) : e '' (e.symm '' Y) = Y := by
    simp only [Set.image_image, e.apply_symm_apply, Set.image_id']
  constructor
  · rintro ⟨g, Fb, Fb', hface, hFb, hFb'⟩
    have hface' : AffineRootSystem.IsFaceOf B₁.affineRoots
        (e.symm '' Fb) (e.symm '' Fb') := by
      apply (AffineRootSystem.isFaceOf_image_transportedRoots_iff e _ _ _).1
      simpa only [hroots, heimage] using hface
    refine ⟨g, e.symm '' Fb, e.symm '' Fb', hface', ?_, ?_⟩
    · apply Φ.injective.image_injective
      rw [image_translatedApartmentMap_of_comparison B₁ B₂ Φ hΦ e hmap,
        heimage]
      exact hFb
    · apply Φ.injective.image_injective
      rw [image_translatedApartmentMap_of_comparison B₁ B₂ Φ hΦ e hmap,
        heimage]
      exact hFb'
  · rintro ⟨g, Fa, Fa', hface, hFa, hFa'⟩
    refine ⟨g, e '' Fa, e '' Fa', ?_, ?_, ?_⟩
    · rw [← hroots]
      exact (AffineRootSystem.isFaceOf_image_transportedRoots_iff e _ _ _).2 hface
    · change Φ '' Fc.val = _
      rw [hFa, image_translatedApartmentMap_of_comparison B₁ B₂ Φ hΦ e hmap]
    · change Φ '' Fc'.val = _
      rw [hFa', image_translatedApartmentMap_of_comparison B₁ B₂ Φ hΦ e hmap]

theorem PolysimplicialRealization.transport_isFaceCompatible
    (R : B₁.PolysimplicialRealization) (hR : R.IsFaceCompatible) :
    (R.transport B₁ B₂ Φ hiso).IsFaceCompatible := by
  intro Fc Fc'
  exact (hR Fc Fc').trans
    (facetPrecedes_facetEquiv_iff B₁ B₂ Φ hiso hΦ e hmap hroots
      (R.realize Fc) (R.realize Fc')).symm

/-- Transfer every clause of the one-group KP building axiom, retaining
the actual torus comparison and source witness. -/
theorem PolysimplicialRealization.transport_satisfiesBuildingAxiom
    (σ : B₁.S ≅ B₂.S) (hσ : B₁.i = CommGroupScheme.groupHom σ.hom ≫ B₂.i)
    (R : B₁.PolysimplicialRealization) (hR : B₁.SatisfiesBuildingAxiom R) :
    B₂.SatisfiesBuildingAxiom (R.transport B₁ B₂ Φ hiso) where
  faceCompatible := R.transport_isFaceCompatible B₁ B₂ Φ hiso hΦ e hmap hroots
    hR.faceCompatible
  isBuilding := by
    change AbstractBuilding.IsBuilding R.complex (R.transport B₁ B₂ Φ hiso).apartments
    rw [R.transport_apartments B₁ B₂ Φ hiso]
    exact hR.isBuilding
  polysimplicialAction := R.transport_isPolysimplicialAction B₁ B₂ Φ hiso hΦ
    hR.polysimplicialAction
  torusApartmentCorrespondence := hasTorusApartmentCorrespondence_of_comparison
    B₁ B₂ Φ hΦ e hmap σ hσ hR.torusApartmentCorrespondence
  normalizerApartmentStabilizer := hasNormalizerApartmentStabilizer_of_comparison
    B₁ B₂ Φ hΦ e hmap σ hσ hR.normalizerApartmentStabilizer

end ValuationBuildingData
end Langlands.Geometry.Building
