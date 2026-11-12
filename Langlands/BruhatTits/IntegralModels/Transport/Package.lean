import Langlands.BruhatTits.IntegralModels.Transport.Model
import Langlands.Geometry.Building.CrossTorusTranslation
import Langlands.Geometry.Building.ValuationBuildingRealizationTransport
import Langlands.Geometry.Building.ValuationBuildingIsoTransport

/-! # Building comparisons used to transport KP model families

A `BuildingTransportPackage B B' f` collects the building-side data along `f : G ≅ H`
needed to carry the subset-indexed model family of KP Axioms 4.1.20 and 4.1.22 from
`B` to `B'`. These are a torus isomorphism with its commuting square, an affine
apartment map with the actual translation derivative, the root comparison, and an
equivariant building map compatible with every translated chart. From these the
module derives the comparisons of bounded subsets, facets, incidences, closures,
fixers and derivative roots.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme Geometry.Building

section Points

variable {k : Type u} [CommRing k] {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- Rational points of `H` are images of rational points of `G` under an isomorphism. -/
theorem rationalPoints_map_hom_inv (f : G ≅ H) (g : rationalPoints H) :
    rationalPoints.map f.hom (rationalPoints.map f.inv g) = g := by
  change (g ≫ f.inv.hom.hom) ≫ f.hom.hom.hom = g
  simp only [Category.assoc, ← Grp.comp_hom_hom, f.inv_hom_id, Grp.id_hom_hom,
    Category.comp_id]

/-- The inverse isomorphism undoes the point map. -/
theorem rationalPoints_map_inv_hom (f : G ≅ H) (g : rationalPoints G) :
    rationalPoints.map f.inv (rationalPoints.map f.hom g) = g := by
  change (g ≫ f.hom.hom.hom) ≫ f.inv.hom.hom = g
  simp only [Category.assoc, ← Grp.comp_hom_hom, f.hom_inv_id, Grp.id_hom_hom,
    Category.comp_id]

end Points

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {G H : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

omit [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] in
/-- The common norm kernel of `H(K)` is the image of that of `G(K)`. -/
theorem map_rationalCommonNormKernel (f : G ≅ H) :
    (Plancherel.rationalCommonNormKernel G).map (rationalPoints.map f.hom) =
      Plancherel.rationalCommonNormKernel H := by
  ext g
  obtain ⟨g, rfl⟩ : ∃ g₀, rationalPoints.map f.hom g₀ = g :=
    ⟨_, rationalPoints_map_hom_inv f g⟩
  rw [Subgroup.mem_map_iff_mem (rationalPoints_map_injective_of_iso f),
    ValuationBuildingData.mem_rationalCommonNormKernel_mapIso_iff]

section AffineEquiv

variable {B₁ : ValuationBuildingData G} {B₂ : ValuationBuildingData H}

/-- Bounded apartment subsets are carried to bounded subsets by an affine equivalence. -/
theorem isBoundedSubset_affineEquiv_image (e : B₁.Apartment ≃ᵃ[ℝ] B₂.Apartment)
    {Ω : Set B₁.Apartment} (hΩ : B₁.IsBoundedSubset Ω) : B₂.IsBoundedSubset (e '' Ω) := by
  intro ψ
  rw [Set.image_image]
  exact hΩ (ψ.comp e.toAffineMap)

/-- Every real affine map of apartments is continuous for the affine topologies. -/
theorem continuous_apartmentAffineMap (φ : B₁.Apartment →ᵃ[ℝ] B₂.Apartment) :
    @Continuous _ _ (affineApartmentTopology B₁) (affineApartmentTopology B₂) φ := by
  let := affineApartmentTopology B₁
  exact continuous_iInf_rng.2 fun ψ =>
    continuous_induced_rng.2 (continuous_affineApartmentFunctional B₁ (ψ.comp φ))

/-- Ordinary apartment closure commutes with an affine equivalence. -/
theorem image_apartmentClosure (e : B₁.Apartment ≃ᵃ[ℝ] B₂.Apartment)
    (Ω : Set B₁.Apartment) :
    e '' apartmentClosure B₁ Ω = apartmentClosure B₂ (e '' Ω) := by
  let := affineApartmentTopology B₁
  let := affineApartmentTopology B₂
  let h : B₁.Apartment ≃ₜ B₂.Apartment :=
    { e.toEquiv with
      continuous_toFun := continuous_apartmentAffineMap e.toAffineMap
      continuous_invFun := continuous_apartmentAffineMap e.symm.toAffineMap }
  exact h.image_closure Ω

end AffineEquiv

/-- Building-side data for transporting KP model families along `f : G ≅ H`: a torus
isomorphism `σ` forming a commuting square with `f`, an affine apartment equivalence
whose derivative is the actual translation map of `σ`, the equality of transported
affine roots, and an `f`-equivariant building equivalence compatible with every
translated apartment chart. -/
structure BuildingTransportPackage (B : ValuationBuildingData G) (B' : ValuationBuildingData H)
    (f : G ≅ H) where
  /-- The isomorphism of maximal split tori. -/
  σ : B.S ≅ B'.S
  /-- The torus inclusions form a commuting square with `f`. -/
  comm : B.i ≫ f.hom = CommGroupScheme.groupHom σ.hom ≫ B'.i
  /-- The affine apartment equivalence. -/
  A : B.Apartment ≃ᵃ[ℝ] B'.Apartment
  /-- Its derivative is the translation map induced by `σ`. -/
  linear : A.linear = translationSpaceTransportEquiv σ f comm
  /-- It carries the affine roots of `B` exactly onto those of `B'`. -/
  roots : AffineRootSystem.transportedRoots A B.affineRoots = B'.affineRoots
  /-- The building equivalence. -/
  Φ : B.ReducedBuilding ≃ B'.ReducedBuilding
  /-- `Φ (g • y) = f(g) • Φ y`. -/
  smul : ∀ (g : rationalPoints G) (y : B.ReducedBuilding),
    Φ (g • y) = rationalPoints.map f.hom g • Φ y
  /-- `Φ` maps the chart of `g · A(S)` to the chart of `f(g) · A(S')` through `A`. -/
  translated : ∀ (g : rationalPoints G) (x : B.Apartment),
    Φ (B.translatedApartmentMap g x) =
      B'.translatedApartmentMap (rationalPoints.map f.hom g) (A x)

namespace BuildingTransportPackage

variable {B : ValuationBuildingData G} {B' : ValuationBuildingData H} {f : G ≅ H}
  (T : BuildingTransportPackage B B' f)

theorem image_symm_image (s : Set B'.Apartment) : T.A '' (T.A.symm '' s) = s :=
  T.A.toEquiv.image_symm_image s

theorem symm_image_image (s : Set B.Apartment) : T.A.symm '' (T.A '' s) = s :=
  T.A.toEquiv.symm_image_image s

/-- The inverse building map on translated charts. -/
theorem symm_translated (g : rationalPoints H) (x : B'.Apartment) :
    T.Φ.symm (B'.translatedApartmentMap g x) =
      B.translatedApartmentMap (rationalPoints.map f.inv g) (T.A.symm x) := by
  apply T.Φ.injective
  rw [Equiv.apply_symm_apply, T.translated, rationalPoints_map_hom_inv,
    AffineEquiv.apply_symm_apply]

theorem image_translated (g : rationalPoints G) (Ωa : Set B.Apartment) :
    T.Φ '' (B.translatedApartmentMap g '' Ωa) =
      B'.translatedApartmentMap (rationalPoints.map f.hom g) '' (T.A '' Ωa) := by
  simp only [Set.image_image, T.translated]

theorem symm_image_translated (g : rationalPoints H) (Ωa : Set B'.Apartment) :
    T.Φ.symm '' (B'.translatedApartmentMap g '' Ωa) =
      B.translatedApartmentMap (rationalPoints.map f.inv g) '' (T.A.symm '' Ωa) := by
  simp only [Set.image_image, T.symm_translated]

/-- Nonempty bounded chart subsets correspond under `Φ`. -/
theorem isNonemptyBoundedApartmentSubset_image_iff (Y : Set B.ReducedBuilding) :
    IsNonemptyBoundedApartmentSubset B' (T.Φ '' Y) ↔ IsNonemptyBoundedApartmentSubset B Y := by
  constructor
  · rintro ⟨g, Ωa, hne, hb, hY⟩
    refine ⟨rationalPoints.map f.inv g, T.A.symm '' Ωa, hne.image _,
      isBoundedSubset_affineEquiv_image T.A.symm hb, ?_⟩
    rw [← T.symm_image_translated, ← hY, T.Φ.symm_image_image]
  · rintro ⟨g, Ωa, hne, hb, rfl⟩
    exact ⟨rationalPoints.map f.hom g, T.A '' Ωa, hne.image _,
      isBoundedSubset_affineEquiv_image T.A hb, T.image_translated g Ωa⟩

/-- Apartment facets correspond under `A`. -/
theorem isFacet_apartment_image_iff (Fa : Set B.Apartment) :
    AffineRootSystem.IsFacet B'.affineRoots (T.A '' Fa) ↔
      AffineRootSystem.IsFacet B.affineRoots Fa :=
  AffineRootSystem.isFacet_image_iff_of_transportedRoots_eq T.A T.roots Fa

/-- The face relation of apartment facets corresponds under `A`. -/
theorem isFaceOf_image_iff (Fa Fa' : Set B.Apartment) :
    AffineRootSystem.IsFaceOf B'.affineRoots (T.A '' Fa) (T.A '' Fa') ↔
      AffineRootSystem.IsFaceOf B.affineRoots Fa Fa' := by
  rw [← T.roots]
  exact AffineRootSystem.isFaceOf_image_transportedRoots_iff T.A _ Fa Fa'

/-- Building facets correspond under `Φ`. -/
theorem isFacet_image_iff (Y : Set B.ReducedBuilding) :
    B'.IsFacet (T.Φ '' Y) ↔ B.IsFacet Y := by
  constructor
  · rintro ⟨g, Fa, hFa, hY⟩
    refine ⟨rationalPoints.map f.inv g, T.A.symm '' Fa, ?_, ?_⟩
    · rw [← T.isFacet_apartment_image_iff, T.image_symm_image]
      exact hFa
    · have hY' : Y = T.Φ.symm '' (B'.translatedApartmentMap g '' Fa) := by
        rw [← T.Φ.symm_image_image Y]
        exact congrArg (T.Φ.symm '' ·) hY
      rw [hY', T.symm_image_translated]
      rfl
  · rintro ⟨g, Fa, hFa, rfl⟩
    exact ⟨rationalPoints.map f.hom g, T.A '' Fa, (T.isFacet_apartment_image_iff Fa).2 hFa,
      T.image_translated g Fa⟩

/-- The bijection of model indices given by images under `Φ`. -/
def indexEquiv : BuildingModelIndex B ≃ BuildingModelIndex B' where
  toFun Ω := ⟨T.Φ '' Ω.val, Ω.property.imp (T.isNonemptyBoundedApartmentSubset_image_iff _).2
    (T.isFacet_image_iff _).2⟩
  invFun Ω := ⟨T.Φ.symm '' Ω.val, by
    have h := Ω.property
    rw [← T.Φ.image_symm_image Ω.val] at h
    exact h.imp (T.isNonemptyBoundedApartmentSubset_image_iff _).1 (T.isFacet_image_iff _).1⟩
  left_inv Ω := Subtype.ext (T.Φ.symm_image_image Ω.val)
  right_inv Ω := Subtype.ext (T.Φ.image_symm_image Ω.val)

@[simp] theorem indexEquiv_val (Ω : BuildingModelIndex B) :
    (T.indexEquiv Ω).val = T.Φ '' Ω.val := rfl

@[simp] theorem indexEquiv_symm_val (Ω : BuildingModelIndex B') :
    (T.indexEquiv.symm Ω).val = T.Φ.symm '' Ω.val := rfl

/-- The bijection of building facets given by images under `Φ`. -/
def facetEquiv : BuildingFacet B ≃ BuildingFacet B' where
  toFun F := ⟨T.Φ '' F.val, (T.isFacet_image_iff _).2 F.property⟩
  invFun F := ⟨T.Φ.symm '' F.val, (T.isFacet_image_iff _).1 (by
    rw [T.Φ.image_symm_image]
    exact F.property)⟩
  left_inv F := Subtype.ext (T.Φ.symm_image_image F.val)
  right_inv F := Subtype.ext (T.Φ.image_symm_image F.val)

@[simp] theorem facetEquiv_val (F : BuildingFacet B) :
    (T.facetEquiv F).val = T.Φ '' F.val := rfl

@[simp] theorem facetEquiv_symm_val (F : BuildingFacet B') :
    (T.facetEquiv.symm F).val = T.Φ.symm '' F.val := rfl

/-- A chart presentation in `B'` gives the corresponding presentation in `B`. -/
theorem symm_val_eq {Y : Set B'.ReducedBuilding} {g : rationalPoints H}
    {Ωa : Set B'.Apartment} (h : Y = B'.translatedApartmentMap g '' Ωa) :
    T.Φ.symm '' Y = B.translatedApartmentMap (rationalPoints.map f.inv g) '' (T.A.symm '' Ωa) := by
  rw [h, T.symm_image_translated]

/-- Facet incidence corresponds under `Φ`. -/
theorem facetPrecedes_facetEquiv_iff (F₁ F₂ : BuildingFacet B) :
    FacetPrecedes B' (T.facetEquiv F₁) (T.facetEquiv F₂) ↔ FacetPrecedes B F₁ F₂ := by
  constructor
  · rintro ⟨g, Fa, Fa', hface, h₁, h₂⟩
    refine ⟨rationalPoints.map f.inv g, T.A.symm '' Fa, T.A.symm '' Fa', ?_, ?_, ?_⟩
    · rw [← T.isFaceOf_image_iff, T.image_symm_image, T.image_symm_image]
      exact hface
    · rw [← T.symm_val_eq h₁]
      exact (T.Φ.symm_image_image F₁.val).symm
    · rw [← T.symm_val_eq h₂]
      exact (T.Φ.symm_image_image F₂.val).symm
  · rintro ⟨g, Fa, Fa', hface, h₁, h₂⟩
    refine ⟨rationalPoints.map f.hom g, T.A '' Fa, T.A '' Fa',
      (T.isFaceOf_image_iff Fa Fa').2 hface, ?_, ?_⟩
    · change T.Φ '' F₁.val = _
      rw [h₁, T.image_translated]
    · change T.Φ '' F₂.val = _
      rw [h₂, T.image_translated]

/-- Incidence in `B'` gives incidence of the corresponding facets of `B`. -/
theorem facetPrecedes_symm {F₁ F₂ : BuildingFacet B'} (h : FacetPrecedes B' F₁ F₂) :
    FacetPrecedes B (T.facetEquiv.symm F₁) (T.facetEquiv.symm F₂) := by
  rw [← T.facetPrecedes_facetEquiv_iff, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h

/-- Incidence in `B` gives incidence of the corresponding facets of `B'`. -/
theorem facetPrecedes_map {F₁ F₂ : BuildingFacet B} (h : FacetPrecedes B F₁ F₂) :
    FacetPrecedes B' (T.facetEquiv F₁) (T.facetEquiv F₂) :=
  (T.facetPrecedes_facetEquiv_iff F₁ F₂).2 h

/-- Closure-ordered pairs in `B'` give closure-ordered pairs in `B`. -/
theorem apartmentSubsetPrecedes_symm {Ω₁ Ω₂ : BuildingModelIndex B'}
    (h : ApartmentSubsetPrecedes B' Ω₁ Ω₂) :
    ApartmentSubsetPrecedes B (T.indexEquiv.symm Ω₁) (T.indexEquiv.symm Ω₂) := by
  obtain ⟨g, Ωa, Ωa', h₁, h₂, hsub⟩ := h
  refine ⟨rationalPoints.map f.inv g, T.A.symm '' Ωa, T.A.symm '' Ωa',
    T.symm_val_eq h₁, T.symm_val_eq h₂, ?_⟩
  rw [← image_apartmentClosure]
  exact Set.image_mono hsub

/-- Every arrow required in `B'` corresponds to an arrow required in `B`. -/
theorem modelMorphismRequired_symm {Ω₁ Ω₂ : BuildingModelIndex B'}
    (h : ModelMorphismRequired B' Ω₁ Ω₂) :
    ModelMorphismRequired B (T.indexEquiv.symm Ω₁) (T.indexEquiv.symm Ω₂) := by
  rcases h with h | ⟨F₁, F₂, h₁, h₂, h⟩
  · exact Or.inl (T.apartmentSubsetPrecedes_symm h)
  · refine Or.inr ⟨T.facetEquiv.symm F₁, T.facetEquiv.symm F₂, ?_, ?_, T.facetPrecedes_symm h⟩
    · change T.Φ.symm '' Ω₁.val = T.Φ.symm '' F₁.val
      rw [h₁]
    · change T.Φ.symm '' Ω₂.val = T.Φ.symm '' F₂.val
      rw [h₂]

/-- The conjugated torus inclusions of corresponding charts form a commuting square. -/
theorem conj_comm (g : rationalPoints H) :
    (B.i ≫ (G.innerIso (rationalPoints.map f.inv g)).hom) ≫ f.hom =
      CommGroupScheme.groupHom T.σ.hom ≫ B'.i ≫ (H.innerIso g).hom := by
  have hg : rationalPoints.map f.inv g ≫ f.hom.hom.hom = g := rationalPoints_map_hom_inv f g
  rw [Category.assoc, innerIso_hom_comp f.hom, hg, ← Category.assoc, T.comm, Category.assoc]

/-- Pointwise fixers correspond under `Φ` and the point map. -/
theorem map_pointwiseFixer (Y : Set B.ReducedBuilding) :
    (B.apartment.pointwiseFixer Y).map (rationalPoints.map f.hom) =
      B'.apartment.pointwiseFixer (T.Φ '' Y) := by
  ext g
  obtain ⟨g, rfl⟩ : ∃ g₀, rationalPoints.map f.hom g₀ = g :=
    ⟨_, rationalPoints_map_hom_inv f g⟩
  rw [Subgroup.mem_map_iff_mem (rationalPoints_map_injective_of_iso f),
    KPApartmentData.mem_pointwiseFixer, KPApartmentData.mem_pointwiseFixer]
  constructor
  · rintro hg _ ⟨y, hy, rfl⟩
    rw [← T.smul, hg y hy]
  · intro hg y hy
    apply T.Φ.injective
    rw [T.smul]
    exact hg _ ⟨y, hy, rfl⟩

/-- Translation by the class of a cocharacter vector is carried along `σ`. -/
theorem A_mk_vadd (v : RealTorusSpace.V B.S) (x : B.Apartment) :
    T.A ((Submodule.Quotient.mk v : TranslationSpace B.i) +ᵥ x) =
      (Submodule.Quotient.mk (RealTorusSpace.cocharacterRealCongr T.σ v) :
        TranslationSpace B'.i) +ᵥ T.A x := by
  rw [T.A.map_vadd, T.linear]
  rfl

/-- Derivative roots of corresponding apartment subsets correspond under `σ`. -/
theorem congr_mem_facetDerivativeRoots_iff (Fa : Set B.Apartment) (a : characterLattice B.S) :
    characterLattice.congr T.σ a ∈ facetDerivativeRoots B' (T.A '' Fa) ↔
      a ∈ facetDerivativeRoots B Fa := by
  constructor
  · rintro ⟨ha', ψ', hψ', hlin, hzero⟩
    have ha : a ∈ relativeRoots B.i := (roots_mem_of_transport_iff T.σ f T.comm a).1 ha'
    rw [← T.roots] at hψ'
    obtain ⟨ψ, hψ, rfl⟩ := hψ'
    refine ⟨ha, ψ, hψ, ?_, ?_⟩
    · apply LinearMap.ext
      intro v
      have hv := LinearMap.congr_fun hlin (T.A.linear v)
      rw [AffineRootSystem.affineFunctionalTransport_linear_apply] at hv
      rw [hv, T.linear]
      exact rootForm_translationSpaceTransportEquiv T.σ f T.comm ⟨a, ha⟩ v
    · intro x hx
      have hx' := hzero (T.A x) ⟨x, hx, rfl⟩
      rwa [AffineRootSystem.affineFunctionalTransport_apply, AffineEquiv.symm_apply_apply] at hx'
  · rintro ⟨ha, ψ, hψ, hlin, hzero⟩
    refine ⟨(roots_mem_of_transport_iff T.σ f T.comm a).2 ha,
      AffineRootSystem.affineFunctionalTransport T.A ψ, T.roots ▸ ⟨ψ, hψ, rfl⟩, ?_, ?_⟩
    · apply LinearMap.ext
      intro w
      obtain ⟨v, rfl⟩ := T.A.linear.surjective w
      rw [AffineRootSystem.affineFunctionalTransport_linear_apply, hlin, T.linear]
      exact (rootForm_translationSpaceTransportEquiv T.σ f T.comm ⟨a, ha⟩ v).symm
    · rintro _ ⟨x, hx, rfl⟩
      rw [AffineRootSystem.affineFunctionalTransport_apply, AffineEquiv.symm_apply_apply]
      exact hzero x hx

end BuildingTransportPackage
end Langlands.BruhatTits.IntegralModels
