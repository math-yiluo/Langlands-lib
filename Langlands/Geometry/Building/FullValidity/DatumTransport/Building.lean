import Langlands.Geometry.Building.FullValidity.DatumTransport.Base

/-!
# Building data and reduced buildings under based group isomorphisms

For `f : G ≅ H`, `σ : S ≅ S'` and `j : S' → H` with `B.i ≫ f = σ ≫ j`, the valuation building
data `B` of `G` give building data of `H` with torus `j`. The apartment class is the image of
the source class, the centralizer is transported along both isomorphisms, and V 6 is the
Library's `transport_basedIso`. The reduced buildings are compared by the quotient map of
`(g, x) ↦ (f(g), x ∘ (σ⁻¹, f⁻¹))`; this map is a building isomorphism in both directions.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel

namespace Langlands.Geometry.Building

open DatumTransport

/-! ### Building isomorphisms from chart data -/

namespace ValuationBuildingData

section Charts

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G₁ G₂ : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G₁.X.hom]
  [IsAffineHom G₂.X.hom]
  {B₁ : ValuationBuildingData G₁} {B₂ : ValuationBuildingData G₂}
  (Φ : B₁.ReducedBuilding ≃ B₂.ReducedBuilding) (φ : rationalPoints G₁ ≃* rationalPoints G₂)
  (A : B₁.Apartment ≃ᵃ[ℝ] B₂.Apartment)
  (hΦ : ∀ g x, Φ (B₁.translatedApartmentMap g x) = B₂.translatedApartmentMap (φ g) (A x))

include hΦ in
/-- The image of a translated apartment subset is the translated image subset. -/
theorem image_translatedApartmentMap_of_chart (g : rationalPoints G₁) (Ω : Set B₁.Apartment) :
    Φ '' (B₁.translatedApartmentMap g '' Ω) = B₂.translatedApartmentMap (φ g) '' (A '' Ω) := by
  rw [Set.image_image, Set.image_image]
  exact Set.image_congr fun x _ => hΦ g x

include hΦ in
/-- The inverse equivalence satisfies the inverse chart identity. -/
theorem symm_chart (g : rationalPoints G₂) (x : B₂.Apartment) :
    Φ.symm (B₂.translatedApartmentMap g x) =
      B₁.translatedApartmentMap (φ.symm g) (A.symm x) := by
  rw [Equiv.symm_apply_eq, hΦ, MulEquiv.apply_symm_apply, AffineEquiv.apply_symm_apply]

include hΦ in
/-- Translated apartment images with an affine-root property in some chart. -/
private theorem exists_chart_image_iff (P₁ : Set B₁.Apartment → Prop)
    (P₂ : Set B₂.Apartment → Prop) (hP : ∀ Ω, P₂ (A '' Ω) ↔ P₁ Ω) (Y : Set B₁.ReducedBuilding) :
    (∃ (g : rationalPoints G₂) (Ω : Set B₂.Apartment), P₂ Ω ∧
        Φ '' Y = B₂.translatedApartmentMap g '' Ω) ↔
      ∃ (g : rationalPoints G₁) (Ω : Set B₁.Apartment), P₁ Ω ∧
        Y = B₁.translatedApartmentMap g '' Ω := by
  constructor
  · rintro ⟨g, Ω, hΩ, hY⟩
    refine ⟨φ.symm g, A.symm '' Ω, ?_, ?_⟩
    · rw [← hP, ← Set.image_comp]
      simpa only [Function.comp_def, AffineEquiv.apply_symm_apply, Set.image_id'] using hΩ
    · apply Set.image_injective.mpr Φ.injective
      rw [hY, image_translatedApartmentMap_of_chart Φ φ A hΦ, MulEquiv.apply_symm_apply]
      congr 1
      exact (A.toEquiv.image_symm_image Ω).symm
  · rintro ⟨g, Ω, hΩ, rfl⟩
    exact ⟨φ g, A '' Ω, (hP Ω).mpr hΩ, image_translatedApartmentMap_of_chart Φ φ A hΦ g Ω⟩

include hΦ in
/-- Facets correspond when the affine roots correspond. -/
theorem isFacet_image_iff_of_chart
    (hroots : AffineRootSystem.transportedRoots A B₁.affineRoots = B₂.affineRoots)
    (Y : Set B₁.ReducedBuilding) : B₂.IsFacet (Φ '' Y) ↔ B₁.IsFacet Y :=
  exists_chart_image_iff Φ φ A hΦ _ _
    (AffineRootSystem.isFacet_image_iff_of_transportedRoots_eq A hroots) Y

include hΦ in
/-- Chambers correspond when the affine roots correspond. -/
theorem isChamber_image_iff_of_chart
    (hroots : AffineRootSystem.transportedRoots A B₁.affineRoots = B₂.affineRoots)
    (Y : Set B₁.ReducedBuilding) : B₂.IsChamber (Φ '' Y) ↔ B₁.IsChamber Y :=
  exists_chart_image_iff Φ φ A hΦ _ _
    (fun Ω => by rw [← hroots]; exact AffineRootSystem.isChamber_image_transportedRoots_iff A _ Ω)
    Y

include hΦ in
/-- Apartments correspond. -/
theorem isApartment_image_iff_of_chart (Y : Set B₁.ReducedBuilding) :
    B₂.IsApartment (Φ '' Y) ↔ B₁.IsApartment Y := by
  have himage (g : rationalPoints G₁) :
      Φ '' (g • B₁.apartmentImage) = φ g • B₂.apartmentImage := by
    rw [← range_translatedApartmentMap, ← range_translatedApartmentMap, ← Set.image_univ,
      image_translatedApartmentMap_of_chart Φ φ A hΦ, Set.image_univ_of_surjective A.surjective,
      Set.image_univ]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨φ.symm g, ?_⟩
    apply Set.image_injective.mpr Φ.injective
    rw [hg, himage, MulEquiv.apply_symm_apply]
  · rintro ⟨g, rfl⟩
    exact ⟨φ g, himage g⟩

include hΦ in
/-- A chart-compatible equivalence with corresponding affine roots is a building isomorphism. -/
theorem isBuildingIso_of_chart
    (hroots : AffineRootSystem.transportedRoots A B₁.affineRoots = B₂.affineRoots) :
    IsBuildingIso B₁ B₂ Φ where
  isFacet_image_iff := isFacet_image_iff_of_chart Φ φ A hΦ hroots
  isApartment_image_iff := isApartment_image_iff_of_chart Φ φ A hΦ
  exists_affineEquiv g := ⟨φ g, A, hΦ g⟩

include hΦ in
/-- The inverse of a chart-compatible equivalence is a building isomorphism. -/
theorem isBuildingIso_symm_of_chart
    (hroots : AffineRootSystem.transportedRoots A B₁.affineRoots = B₂.affineRoots) :
    IsBuildingIso B₂ B₁ Φ.symm :=
  isBuildingIso_of_chart Φ.symm φ.symm A.symm (symm_chart Φ φ A hΦ) (by
    rw [← hroots, AffineRootSystem.transportedRoots_symm])

end Charts

/-! ### The transported building data -/

section Transport

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (B : ValuationBuildingData G) {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {j : S.toGrp ⟶ H} (σ : B.S ≅ S) (f : G ≅ H)
  (h : B.i ≫ f.hom = CommGroupScheme.groupHom σ.hom ≫ j)

omit [IsAffineHom H.X.hom] in
include h in
/-- The prescribed target torus is a maximal split torus of `H`. -/
theorem isMaximalSplitTorus_of_basedIso : IsMaximalSplitTorus j := by
  rw [target_eq σ f h]
  exact isMaximalSplitTorus_torusIso_comp (B.isMaximalSplitTorus.comp_iso f) σ.symm

/-- The building data of `H` with torus `j`: the image of the apartment class of `B`, the
transported centralizer and V 6 from `KPApartmentData.IsOmegaCompatible.transport_basedIso`. -/
def basedTransport : ValuationBuildingData H where
  isConnectedReductive := B.isConnectedReductive.of_iso f.symm
  S := S
  i := j
  isMaximalSplitTorus := B.isMaximalSplitTorus_of_basedIso σ f h
  apartment :=
    have := mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus_of_basedIso σ f h)
    B.apartment.transport σ f h
  centralizer := B.centralizer.basedTransport σ f h
  isOmegaCompatible :=
    have := mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus_of_basedIso σ f h)
    B.isOmegaCompatible.transport_basedIso B.centralizer _ σ f h

@[simp] theorem basedTransport_S : (B.basedTransport σ f h).S = S := rfl

@[simp] theorem basedTransport_i : (B.basedTransport σ f h).i = j := rfl

theorem basedTransport_apartment :
    have := mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus_of_basedIso σ f h)
    (B.basedTransport σ f h).apartment = B.apartment.transport σ f h := rfl

/-- The affine comparison `A(S) ≃ A(S')` of the apartments. -/
def basedApartmentEquiv : B.Apartment ≃ᵃ[ℝ] (B.basedTransport σ f h).Apartment :=
  have := mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus_of_basedIso σ f h)
  B.apartment.apartmentTransportAffineEquiv σ f h

/-- The comparison `B(G) ≃ B(H)` of the reduced buildings. -/
def basedBuildingEquiv : B.ReducedBuilding ≃ (B.basedTransport σ f h).ReducedBuilding :=
  have := mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus_of_basedIso σ f h)
  B.apartment.reducedBuildingTransportEquiv σ f h

theorem basedBuildingEquiv_smul (g : rationalPoints G) (y : B.ReducedBuilding) :
    B.basedBuildingEquiv σ f h (g • y) =
      rationalPoints.map f.hom g • B.basedBuildingEquiv σ f h y :=
  have := mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus_of_basedIso σ f h)
  B.apartment.reducedBuildingTransportEquiv_smul σ f h g y

theorem basedBuildingEquiv_apartmentMap (x : B.Apartment) :
    B.basedBuildingEquiv σ f h (B.apartmentMap x) =
      (B.basedTransport σ f h).apartmentMap (B.basedApartmentEquiv σ f h x) :=
  have := mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus_of_basedIso σ f h)
  B.apartment.reducedBuildingTransportEquiv_apartmentMap σ f h x

theorem basedBuildingEquiv_translatedApartmentMap (g : rationalPoints G) (x : B.Apartment) :
    B.basedBuildingEquiv σ f h (B.translatedApartmentMap g x) =
      (B.basedTransport σ f h).translatedApartmentMap (pointsEquiv f g)
        (B.basedApartmentEquiv σ f h x) := by
  rw [translatedApartmentMap, basedBuildingEquiv_smul, basedBuildingEquiv_apartmentMap]
  rfl

/-- The affine roots of the target are the transported affine roots. -/
theorem transportedRoots_basedApartmentEquiv :
    AffineRootSystem.transportedRoots (B.basedApartmentEquiv σ f h) B.affineRoots =
      (B.basedTransport σ f h).affineRoots :=
  have := mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus_of_basedIso σ f h)
  B.apartment.transported_affineRoots_transport σ f h

theorem isBuildingIso_basedBuildingEquiv :
    IsBuildingIso B (B.basedTransport σ f h) (B.basedBuildingEquiv σ f h) :=
  isBuildingIso_of_chart _ (pointsEquiv f) _ (B.basedBuildingEquiv_translatedApartmentMap σ f h)
    (B.transportedRoots_basedApartmentEquiv σ f h)

theorem isBuildingIso_basedBuildingEquiv_symm :
    IsBuildingIso (B.basedTransport σ f h) B (B.basedBuildingEquiv σ f h).symm :=
  isBuildingIso_symm_of_chart _ (pointsEquiv f) _
    (B.basedBuildingEquiv_translatedApartmentMap σ f h)
    (B.transportedRoots_basedApartmentEquiv σ f h)

theorem isEquivariantBuildingIso_basedBuildingEquiv :
    IsEquivariantBuildingIso B (B.basedTransport σ f h) (rationalPoints.map f.hom)
      (B.basedBuildingEquiv σ f h) :=
  ⟨B.isBuildingIso_basedBuildingEquiv σ f h, B.basedBuildingEquiv_smul σ f h⟩

theorem isFacet_basedBuildingEquiv_image_iff (Y : Set B.ReducedBuilding) :
    (B.basedTransport σ f h).IsFacet (B.basedBuildingEquiv σ f h '' Y) ↔ B.IsFacet Y :=
  isFacet_image_iff_of_chart _ (pointsEquiv f) _
    (B.basedBuildingEquiv_translatedApartmentMap σ f h)
    (B.transportedRoots_basedApartmentEquiv σ f h) Y

theorem isChamber_basedBuildingEquiv_image_iff (Y : Set B.ReducedBuilding) :
    (B.basedTransport σ f h).IsChamber (B.basedBuildingEquiv σ f h '' Y) ↔ B.IsChamber Y :=
  isChamber_image_iff_of_chart _ (pointsEquiv f) _
    (B.basedBuildingEquiv_translatedApartmentMap σ f h)
    (B.transportedRoots_basedApartmentEquiv σ f h) Y

theorem isApartment_basedBuildingEquiv_image_iff (Y : Set B.ReducedBuilding) :
    (B.basedTransport σ f h).IsApartment (B.basedBuildingEquiv σ f h '' Y) ↔
      B.IsApartment Y :=
  isApartment_image_iff_of_chart _ (pointsEquiv f) _
    (B.basedBuildingEquiv_translatedApartmentMap σ f h) Y

/-- Full point stabilizers are carried to full point stabilizers. -/
theorem map_fixer_basedTransport (y : B.ReducedBuilding) :
    (B.fixer y).map (rationalPoints.map f.hom) =
      (B.basedTransport σ f h).fixer (B.basedBuildingEquiv σ f h y) :=
  have := mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus_of_basedIso σ f h)
  B.apartment.map_reducedFixer_transport σ f h y

/-- Pointwise fixers of subsets are carried to pointwise fixers of their images. -/
theorem map_pointwiseFixer_basedTransport (Y : Set B.ReducedBuilding) :
    (B.pointwiseFixer Y).map (rationalPoints.map f.hom) =
      (B.basedTransport σ f h).pointwiseFixer (B.basedBuildingEquiv σ f h '' Y) := by
  ext y
  obtain ⟨g, rfl⟩ := (pointsEquiv f).surjective y
  rw [pointsEquiv_apply, mem_map_iff, KPApartmentData.mem_pointwiseFixer,
    KPApartmentData.mem_pointwiseFixer]
  constructor
  · rintro hg _ ⟨z, hz, rfl⟩
    rw [← basedBuildingEquiv_smul, hg z hz]
  · intro hg z hz
    apply (B.basedBuildingEquiv σ f h).injective
    rw [basedBuildingEquiv_smul]
    exact hg _ ⟨z, hz, rfl⟩

/-- Norm-one stabilizers are carried to norm-one stabilizers. -/
theorem map_compactStabilizer_basedTransport (y : B.ReducedBuilding) :
    (B.compactStabilizer y).map (rationalPoints.map f.hom) =
      (B.basedTransport σ f h).compactStabilizer (B.basedBuildingEquiv σ f h y) := by
  ext z
  obtain ⟨g, rfl⟩ := (pointsEquiv f).surjective z
  rw [pointsEquiv_apply, mem_map_iff, B.mem_compactStabilizer,
    (B.basedTransport σ f h).mem_compactStabilizer, mem_rationalCommonNormKernel_mapIso_iff,
    ← basedBuildingEquiv_smul]
  exact and_congr_right fun _ => (B.basedBuildingEquiv σ f h).injective.eq_iff.symm

end Transport

end ValuationBuildingData

/-! ### Parahoric data -/

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (P : ParahoricBuildingData G) {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {j : S.toGrp ⟶ H} (σ : P.S ≅ S) (f : G ≅ H)
  (h : P.i ≫ f.hom = CommGroupScheme.groupHom σ.hom ≫ j)

/-- Parahoric building data of `H` with torus `j`, with the transported zero-subgroup data. -/
def basedTransport : ParahoricBuildingData H where
  toValuationBuildingData := P.toValuationBuildingData.basedTransport σ f h
  zeroDatum := P.zeroDatum.basedTransport σ f h

@[simp] theorem basedTransport_toValuationBuildingData :
    (P.basedTransport σ f h).toValuationBuildingData =
      P.toValuationBuildingData.basedTransport σ f h := rfl

/-- `G(F)^0` is carried onto `H(F)^0`. -/
theorem basedTransport_zeroSubgroup :
    (P.basedTransport σ f h).zeroSubgroup = P.zeroSubgroup.map (rationalPoints.map f.hom) :=
  P.zeroDatum.basedTransport_zeroSubgroup σ f h

end ParahoricBuildingData

end Langlands.Geometry.Building
