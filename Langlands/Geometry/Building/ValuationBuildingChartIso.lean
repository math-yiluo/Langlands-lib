import Langlands.Geometry.Building.AffineFacetTransport
import Langlands.Geometry.Building.ValuationBuildingApartmentCharts
import Langlands.Geometry.Building.FullValidity.Assignment

/-!
# Chart isomorphisms of reduced buildings

A map `Φ : B(D₁) → B(D₂)` between the reduced buildings of two apartment data, possibly over
different fields, is a *chart isomorphism* along a group homomorphism `θ`, a base point `c` and
an affine equivalence `e` of apartments when `Φ(g · x) = (θ(g) c) · e(x)` for all `g` and all
apartment points `x`, and `e` carries the affine roots onto the affine roots. Chart isomorphisms
compose, contain the translations, and arise from any group isomorphism and apartment
equivalence matching the normalizers and the sharp fixers. A chart isomorphism of building data
along a surjective `θ` is an equivariant isomorphism of buildings.
-/

noncomputable section

universe u uH₁ uH₂ uA₁ uA₂

open CategoryTheory AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace ApartmentQuotient

variable {H₁ : Type uH₁} {H₂ : Type uH₂} [Group H₁] [Group H₂]
  {N₁ : Subgroup H₁} {N₂ : Subgroup H₂} {A₁ : Type uA₁} {A₂ : Type uA₂}
  [MulAction N₁ A₁] [MulAction N₂ A₂]
  (θ : H₁ ≃* H₂) (e : A₁ ≃ A₂) (hN : ∀ g, θ g ∈ N₂ ↔ g ∈ N₁)

/-- The element `θ(n)` of `N₂` for `n ∈ N₁`. -/
def congrNormalizer (n : N₁) : N₂ :=
  ⟨θ n, (hN n).2 n.2⟩

@[simp] theorem coe_congrNormalizer (n : N₁) : (congrNormalizer θ hN n : H₂) = θ n :=
  rfl

variable {θ hN}

/-- A group isomorphism and an equivalence of `N`-sets matching the normalizers and the subgroup
families identify the relations (4.4.2). -/
theorem apartmentRel_congr_iff (P₁ : A₁ → Subgroup H₁) (P₂ : A₂ → Subgroup H₂)
    (he : ∀ (n : N₁) (x : A₁), e (n • x) = congrNormalizer θ hN n • e x)
    (hP : ∀ x g, θ g ∈ P₂ (e x) ↔ g ∈ P₁ x) (a b : H₁ × A₁) :
    apartmentRel N₁ P₁ a b ↔ apartmentRel N₂ P₂ (θ a.1, e a.2) (θ b.1, e b.2) := by
  constructor
  · rintro ⟨n, hn, hmem⟩
    refine ⟨congrNormalizer θ hN n, by rw [← he, hn], ?_⟩
    rw [coe_congrNormalizer, ← map_inv, ← map_mul, ← map_mul]
    exact (hP _ _).2 hmem
  · rintro ⟨n', hn', hmem'⟩
    have hn₁ : θ.symm n' ∈ N₁ := (hN _).1 (by rw [MulEquiv.apply_symm_apply]; exact n'.2)
    let n : N₁ := ⟨θ.symm n', hn₁⟩
    have hnn' : congrNormalizer θ hN n = n' :=
      Subtype.ext (by rw [coe_congrNormalizer]; exact θ.apply_symm_apply _)
    refine ⟨n, e.injective (by rw [he, hnn']; exact hn'), ?_⟩
    apply (hP _ _).1
    rw [map_mul, map_mul, map_inv]
    change (θ a.1)⁻¹ * θ b.1 * θ (θ.symm n') ∈ P₂ (e a.2)
    rwa [MulEquiv.apply_symm_apply]

/-- The equivalence of apartment quotients `[(g, x)] ↦ [(θ(g), e(x))]`. -/
def congrEquiv (P₁ : CovariantSubgroupFamily N₁ A₁) (P₂ : CovariantSubgroupFamily N₂ A₂)
    (he : ∀ (n : N₁) (x : A₁), e (n • x) = congrNormalizer θ hN n • e x)
    (hP : ∀ x g, θ g ∈ P₂ (e x) ↔ g ∈ P₁ x) :
    ApartmentQuotient P₁ ≃ ApartmentQuotient P₂ :=
  Quotient.congr (Equiv.prodCongr θ.toEquiv e)
    (fun a b => apartmentRel_congr_iff e P₁ P₂ he hP a b)

@[simp] theorem congrEquiv_mk (P₁ : CovariantSubgroupFamily N₁ A₁)
    (P₂ : CovariantSubgroupFamily N₂ A₂)
    (he : ∀ (n : N₁) (x : A₁), e (n • x) = congrNormalizer θ hN n • e x)
    (hP : ∀ x g, θ g ∈ P₂ (e x) ↔ g ∈ P₁ x) (g : H₁) (x : A₁) :
    congrEquiv e P₁ P₂ he hP (mk P₁ (g, x)) = mk P₂ (θ g, e x) :=
  rfl

end ApartmentQuotient

namespace KPApartmentData

section ChartIso

variable {k₁ k₂ k₃ : Type u} [Field k₁] [Field k₂] [Field k₃]
  {S₁ : CommGroupScheme (Spec (CommRingCat.of k₁))}
  {G₁ : GroupScheme (Spec (CommRingCat.of k₁))} {i₁ : S₁.toGrp ⟶ G₁}
  [Mono i₁.hom.hom.left] [IsAffineHom G₁.X.hom] {ω₁ : k₁ˣ → ℝ}
  {S₂ : CommGroupScheme (Spec (CommRingCat.of k₂))}
  {G₂ : GroupScheme (Spec (CommRingCat.of k₂))} {i₂ : S₂.toGrp ⟶ G₂}
  [Mono i₂.hom.hom.left] [IsAffineHom G₂.X.hom] {ω₂ : k₂ˣ → ℝ}
  {S₃ : CommGroupScheme (Spec (CommRingCat.of k₃))}
  {G₃ : GroupScheme (Spec (CommRingCat.of k₃))} {i₃ : S₃.toGrp ⟶ G₃}
  [Mono i₃.hom.hom.left] [IsAffineHom G₃.X.hom] {ω₃ : k₃ˣ → ℝ}

/-- `Φ : B(D₁) → B(D₂)` is given in the apartment charts by `Φ(g · x) = (θ(g) c) · e(x)`, and
`e` carries the affine roots of `D₁` onto those of `D₂`. -/
structure IsChartIso (D₁ : KPApartmentData i₁ ω₁) (D₂ : KPApartmentData i₂ ω₂)
    (θ : rationalPoints G₁ →* rationalPoints G₂) (c : rationalPoints G₂)
    (e : D₁.Apartment ≃ᵃ[ℝ] D₂.Apartment) (Φ : D₁.ReducedBuilding ≃ D₂.ReducedBuilding) :
    Prop where
  /-- The chart formula `Φ(g · x) = (θ(g) c) · e(x)`. -/
  map_smul_apartmentMap : ∀ (g : rationalPoints G₁) (x : D₁.Apartment),
    Φ (g • D₁.apartmentMap x) = (θ g * c) • D₂.apartmentMap (e x)
  /-- `e` carries the affine roots onto the affine roots. -/
  transportedRoots_eq : AffineRootSystem.transportedRoots e D₁.affineRoots = D₂.affineRoots

theorem transportedRoots_refl {V A : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
    (Ψ : Set (A →ᵃ[ℝ] ℝ)) : AffineRootSystem.transportedRoots (AffineEquiv.refl ℝ A) Ψ = Ψ := by
  ext ψ
  constructor
  · rintro ⟨ζ, hζ, rfl⟩
    have : AffineRootSystem.affineFunctionalTransport (AffineEquiv.refl ℝ A) ζ = ζ := by
      ext; rfl
    rwa [this]
  · intro hψ
    exact ⟨ψ, hψ, rfl⟩

theorem transportedRoots_trans {V W X A B C : Type*} [AddCommGroup V] [Module ℝ V]
    [AddTorsor V A] [AddCommGroup W] [Module ℝ W] [AddTorsor W B]
    [AddCommGroup X] [Module ℝ X] [AddTorsor X C]
    (a : A ≃ᵃ[ℝ] B) (b : B ≃ᵃ[ℝ] C) (Ψ : Set (A →ᵃ[ℝ] ℝ)) :
    AffineRootSystem.transportedRoots (a.trans b) Ψ =
      AffineRootSystem.transportedRoots b (AffineRootSystem.transportedRoots a Ψ) := by
  simp only [AffineRootSystem.transportedRoots, Set.image_image]
  congr 1

namespace IsChartIso

variable {D₁ : KPApartmentData i₁ ω₁} {D₂ : KPApartmentData i₂ ω₂}
  {D₃ : KPApartmentData i₃ ω₃}

/-- The identity is a chart isomorphism. -/
theorem refl (D : KPApartmentData i₁ ω₁) :
    IsChartIso D D (MonoidHom.id _) 1 (AffineEquiv.refl ℝ _) (Equiv.refl _) where
  map_smul_apartmentMap g x := by simp
  transportedRoots_eq := transportedRoots_refl _

/-- Chart isomorphisms compose. -/
theorem trans {θ₁ : rationalPoints G₁ →* rationalPoints G₂} {c₁ : rationalPoints G₂}
    {e₁ : D₁.Apartment ≃ᵃ[ℝ] D₂.Apartment} {Φ₁ : D₁.ReducedBuilding ≃ D₂.ReducedBuilding}
    {θ₂ : rationalPoints G₂ →* rationalPoints G₃} {c₂ : rationalPoints G₃}
    {e₂ : D₂.Apartment ≃ᵃ[ℝ] D₃.Apartment} {Φ₂ : D₂.ReducedBuilding ≃ D₃.ReducedBuilding}
    (h₁ : IsChartIso D₁ D₂ θ₁ c₁ e₁ Φ₁) (h₂ : IsChartIso D₂ D₃ θ₂ c₂ e₂ Φ₂) :
    IsChartIso D₁ D₃ (θ₂.comp θ₁) (θ₂ c₁ * c₂) (e₁.trans e₂) (Φ₁.trans Φ₂) where
  map_smul_apartmentMap g x := by
    rw [Equiv.trans_apply, h₁.map_smul_apartmentMap, h₂.map_smul_apartmentMap,
      AffineEquiv.trans_apply, MonoidHom.comp_apply, map_mul, mul_assoc]
  transportedRoots_eq := by
    rw [transportedRoots_trans, h₁.transportedRoots_eq, h₂.transportedRoots_eq]

/-- Translation by `c` is a chart isomorphism along conjugation by `c`, with base point `c`. -/
theorem smul (D : KPApartmentData i₁ ω₁) (c : rationalPoints G₁) :
    IsChartIso D D (MulAut.conj c).toMonoidHom c (AffineEquiv.refl ℝ _)
      (MulAction.toPerm c) where
  map_smul_apartmentMap g x := by
    rw [MulAction.toPerm_apply, smul_smul, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      inv_mul_cancel_right, AffineEquiv.refl_apply]
  transportedRoots_eq := transportedRoots_refl _

end IsChartIso

variable (D₁ : KPApartmentData i₁ ω₁) (D₂ : KPApartmentData i₂ ω₂)
  (θ : rationalPoints G₁ ≃* rationalPoints G₂) (e : D₁.Apartment ≃ᵃ[ℝ] D₂.Apartment)
  (hN : ∀ g, θ g ∈ normalizerPoints i₂ ↔ g ∈ normalizerPoints i₁)
  (he : ∀ (n : normalizerPoints i₁) (x : D₁.Apartment),
    e (n • x) = ApartmentQuotient.congrNormalizer θ hN n • e x)
  (hP : ∀ (x : D₁.Apartment) (g : rationalPoints G₁),
    θ g ∈ D₂.sharpFixer {e x} ↔ g ∈ D₁.sharpFixer {x})

/-- The equivalence of reduced buildings `[(g, x)] ↦ [(θ(g), e(x))]` for a group isomorphism and
an apartment equivalence matching the normalizers and the sharp fixers. -/
def congrBuildingEquiv : D₁.ReducedBuilding ≃ D₂.ReducedBuilding :=
  ApartmentQuotient.congrEquiv e.toEquiv D₁.sharpFixerFamily D₂.sharpFixerFamily he hP

theorem congrBuildingEquiv_mk (g : rationalPoints G₁) (x : D₁.Apartment) :
    congrBuildingEquiv D₁ D₂ θ e hN he hP (ApartmentQuotient.mk D₁.sharpFixerFamily (g, x)) =
      ApartmentQuotient.mk D₂.sharpFixerFamily (θ g, e x) :=
  rfl

/-- The congruence equivalence is a chart isomorphism with base point `1`. -/
theorem isChartIso_congrBuildingEquiv
    (hroots : AffineRootSystem.transportedRoots e D₁.affineRoots = D₂.affineRoots) :
    IsChartIso D₁ D₂ θ.toMonoidHom 1 e (congrBuildingEquiv D₁ D₂ θ e hN he hP) where
  map_smul_apartmentMap g x := by
    change congrBuildingEquiv D₁ D₂ θ e hN he hP
        (g • ApartmentQuotient.mk D₁.sharpFixerFamily (1, x)) =
      (θ g * 1) • ApartmentQuotient.mk D₂.sharpFixerFamily (1, e x)
    rw [ApartmentQuotient.smul_mk, ApartmentQuotient.smul_mk, congrBuildingEquiv_mk,
      mul_one, mul_one, mul_one]
  transportedRoots_eq := hroots

end ChartIso

end KPApartmentData

namespace ValuationBuildingData

variable {F₁ F₂ : Type u} [Field F₁] [ValuativeRel F₁] [TopologicalSpace F₁]
  [IsNonarchimedeanLocalField F₁] [Field F₂] [ValuativeRel F₂] [TopologicalSpace F₂]
  [IsNonarchimedeanLocalField F₂]
  {G₁ : GroupScheme (Spec (CommRingCat.of F₁))} [IsAffineHom G₁.X.hom]
  {G₂ : GroupScheme (Spec (CommRingCat.of F₂))} [IsAffineHom G₂.X.hom]
  {B₁ : ValuationBuildingData G₁} {B₂ : ValuationBuildingData G₂}
  {θ : rationalPoints G₁ →* rationalPoints G₂} {c : rationalPoints G₂}
  {e : B₁.Apartment ≃ᵃ[ℝ] B₂.Apartment} {Φ : B₁.ReducedBuilding ≃ B₂.ReducedBuilding}

/-- The image of a translated apartment subset under a chart isomorphism. -/
theorem image_translatedApartmentMap_of_isChartIso
    (h : B₁.apartment.IsChartIso B₂.apartment θ c e Φ) (g : rationalPoints G₁)
    (Fa : Set B₁.Apartment) :
    Φ '' ((fun x => g • B₁.apartmentMap x) '' Fa) =
      (fun x => (θ g * c) • B₂.apartmentMap x) '' (e '' Fa) := by
  rw [Set.image_image, Set.image_image]
  exact Set.image_congr fun x _ => h.map_smul_apartmentMap g x

theorem image_apartmentImage_of_isChartIso
    (h : B₁.apartment.IsChartIso B₂.apartment θ c e Φ) (g : rationalPoints G₁) :
    Φ '' (g • B₁.apartmentImage) = (θ g * c) • B₂.apartmentImage := by
  rw [← B₁.range_translatedApartmentMap, ← B₂.range_translatedApartmentMap,
    ← Set.image_univ, ← Set.image_univ]
  change Φ '' ((fun x => g • B₁.apartmentMap x) '' Set.univ) =
    (fun x => (θ g * c) • B₂.apartmentMap x) '' Set.univ
  rw [image_translatedApartmentMap_of_isChartIso h, Set.image_univ_of_surjective e.surjective]

/-- A chart isomorphism along a surjective group homomorphism is an equivariant isomorphism of
buildings. -/
theorem isEquivariantBuildingIso_of_isChartIso (hθ : Function.Surjective θ)
    (h : B₁.apartment.IsChartIso B₂.apartment θ c e Φ) :
    IsEquivariantBuildingIso B₁ B₂ θ Φ := by
  refine ⟨⟨fun Y => ?_, fun Y => ?_, fun g₁ => ⟨θ g₁ * c, e, fun x => ?_⟩⟩, fun g y => ?_⟩
  · constructor
    · rintro ⟨g₂, Fa₂, hFa₂, hY⟩
      obtain ⟨g₁, hg₁⟩ := hθ (g₂ * c⁻¹)
      have himage : e '' (e.symm '' Fa₂) = Fa₂ := e.toEquiv.image_symm_image Fa₂
      refine ⟨g₁, e.symm '' Fa₂, ?_, Φ.injective.image_injective ?_⟩
      · apply (AffineRootSystem.isFacet_image_iff_of_transportedRoots_eq e
          h.transportedRoots_eq _).1
        rwa [himage]
      · rw [hY, image_translatedApartmentMap_of_isChartIso h, himage, hg₁, inv_mul_cancel_right]
    · rintro ⟨g, Fa, hFa, rfl⟩
      exact ⟨θ g * c, e '' Fa,
        (AffineRootSystem.isFacet_image_iff_of_transportedRoots_eq e h.transportedRoots_eq
          Fa).2 hFa, image_translatedApartmentMap_of_isChartIso h g Fa⟩
  · constructor
    · rintro ⟨g₂, hY⟩
      obtain ⟨g₁, hg₁⟩ := hθ (g₂ * c⁻¹)
      refine ⟨g₁, Φ.injective.image_injective ?_⟩
      rw [hY, image_apartmentImage_of_isChartIso h, hg₁, inv_mul_cancel_right]
    · rintro ⟨g, rfl⟩
      exact ⟨θ g * c, image_apartmentImage_of_isChartIso h g⟩
  · exact h.map_smul_apartmentMap g₁ x
  · obtain ⟨g', x, rfl⟩ := B₁.exists_smul_apartmentMap y
    rw [smul_smul, h.map_smul_apartmentMap, h.map_smul_apartmentMap, map_mul, mul_assoc,
      mul_smul]

end ValuationBuildingData

end Langlands.Geometry.Building
