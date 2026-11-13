import Langlands.Geometry.Building.NormalizerAffineRootAction
import Langlands.Geometry.Building.AffineFacetTransport
import Langlands.Geometry.Building.ValuationBuildingApartmentCharts
import Langlands.Geometry.Building.FullValidity.Assignment

/-!
# Valuation-building quotients compared along a group homomorphism

`ApartmentQuotient.homEquiv` compares two apartment quotients along a homomorphism
`θ : H₁ →* H₂` and a bijection `ε : A₁ ≃ A₂` of apartments. `KPApartmentData.Transfer`
bundles the corresponding data for two apartment classes, and
`KPApartmentData.Transfer.isEquivariantBuildingIso` shows that the induced map of reduced
buildings is an equivariant building isomorphism.
-/

noncomputable section

universe u v₁ v₂ w₁ w₂

open CategoryTheory AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace ApartmentQuotient

section HomMap

variable {H₁ : Type v₁} {H₂ : Type v₂} [Group H₁] [Group H₂]
  {N₁ : Subgroup H₁} {N₂ : Subgroup H₂} {A₁ : Type w₁} {A₂ : Type w₂}
  [MulAction N₁ A₁] [MulAction N₂ A₂]
  (P₁ : CovariantSubgroupFamily N₁ A₁) (P₂ : CovariantSubgroupFamily N₂ A₂)

/-- Hypotheses under which `[(g, x)] ↦ [(θ g, ε x)]` is a well-defined bijection between the
quotients for `P₁` and `P₂`: `θ` maps `N₁` into `N₂` compatibly with `ε`, maps each `P₁ x`
onto `P₂ (ε x)`, pulls `N₂` back into `N₁`, and `H₂ = θ(H₁) · N₂`. -/
structure IsHomComparison (θ : H₁ →* H₂) (ε : A₁ ≃ A₂) : Prop where
  map_mem : ∀ n : N₁, θ n ∈ N₂
  map_smul : ∀ (n : N₁) (x : A₁), ε (n • x) = (⟨θ n, map_mem n⟩ : N₂) • ε x
  map_family : ∀ x, (P₁ x).map θ = P₂ (ε x)
  mem_of_map_mem : ∀ g, θ g ∈ N₂ → g ∈ N₁
  exists_mul : ∀ h : H₂, ∃ (g : H₁) (n : N₂), h = θ g * n

variable {P₁ P₂} {θ : H₁ →* H₂} {ε : A₁ ≃ A₂}

theorem IsHomComparison.apartmentRel (hc : IsHomComparison P₁ P₂ θ ε) {a b : H₁ × A₁}
    (hab : apartmentRel N₁ P₁ a b) :
    apartmentRel N₂ P₂ (θ a.1, ε a.2) (θ b.1, ε b.2) := by
  obtain ⟨n, hn, hmem⟩ := hab
  refine ⟨⟨θ n, hc.map_mem n⟩, by rw [← hc.map_smul, hn], ?_⟩
  change (θ a.1)⁻¹ * θ b.1 * θ n ∈ P₂ (ε a.2)
  rw [← hc.map_family]
  exact ⟨_, hmem, by simp only [map_mul, map_inv]⟩

/-- The map `[(g, x)] ↦ [(θ g, ε x)]`. -/
def homMap (hc : IsHomComparison P₁ P₂ θ ε) : ApartmentQuotient P₁ → ApartmentQuotient P₂ :=
  Quotient.map' (fun a : H₁ × A₁ => (θ a.1, ε a.2)) (fun _ _ hab => hc.apartmentRel hab)

theorem homMap_mk (hc : IsHomComparison P₁ P₂ θ ε) (g : H₁) (x : A₁) :
    homMap hc (mk P₁ (g, x)) = mk P₂ (θ g, ε x) :=
  rfl

theorem homMap_apartment (hc : IsHomComparison P₁ P₂ θ ε) (x : A₁) :
    homMap hc (apartment P₁ x) = apartment P₂ (ε x) := by
  rw [apartment, homMap_mk, map_one]
  rfl

theorem homMap_smul (hc : IsHomComparison P₁ P₂ θ ε) (h : H₁) (q : ApartmentQuotient P₁) :
    homMap hc (h • q) = θ h • homMap hc q := by
  induction q using ind with
  | h g x => rw [smul_mk, homMap_mk, homMap_mk, smul_mk, map_mul]

theorem homMap_injective (hc : IsHomComparison P₁ P₂ θ ε) : Function.Injective (homMap hc) := by
  intro q q'
  induction q using ind with
  | h g x =>
    induction q' using ind with
    | h h y =>
      intro hq
      rw [homMap_mk, homMap_mk, mk_eq_mk_iff] at hq
      obtain ⟨n', hn', hmem⟩ := hq
      rw [← hc.map_family] at hmem
      obtain ⟨p, hp, hpe⟩ := hmem
      have hθm : θ (h⁻¹ * g * p) = n' := by
        rw [map_mul, map_mul, map_inv, hpe]
        group
      have hm : h⁻¹ * g * p ∈ N₁ := hc.mem_of_map_mem _ (hθm ▸ n'.2)
      rw [mk_eq_mk_iff]
      refine ⟨⟨h⁻¹ * g * p, hm⟩, ?_, ?_⟩
      · apply ε.injective
        rw [hc.map_smul, ← hn']
        congr 1
        exact Subtype.ext hθm
      · change g⁻¹ * h * (h⁻¹ * g * p) ∈ P₁ x
        simpa [mul_assoc] using hp

theorem homMap_surjective (hc : IsHomComparison P₁ P₂ θ ε) :
    Function.Surjective (homMap hc) := by
  intro q
  induction q using ind with
  | h h y =>
    obtain ⟨g, n, rfl⟩ := hc.exists_mul h
    refine ⟨mk P₁ (g, ε.symm (n • y)), ?_⟩
    rw [homMap_mk, Equiv.apply_symm_apply, mk_eq_mk_iff]
    refine ⟨n⁻¹, inv_smul_smul n y, ?_⟩
    change (θ g)⁻¹ * (θ g * (n : H₂)) * (n : H₂)⁻¹ ∈ P₂ (n • y)
    simp only [inv_mul_cancel_left, mul_inv_cancel]
    exact one_mem _

/-- The bijection `[(g, x)] ↦ [(θ g, ε x)]` of quotients. -/
def homEquiv (hc : IsHomComparison P₁ P₂ θ ε) : ApartmentQuotient P₁ ≃ ApartmentQuotient P₂ :=
  Equiv.ofBijective (homMap hc) ⟨homMap_injective hc, homMap_surjective hc⟩

@[simp] theorem homEquiv_apply (hc : IsHomComparison P₁ P₂ θ ε) (q : ApartmentQuotient P₁) :
    homEquiv hc q = homMap hc q :=
  rfl

end HomMap

end ApartmentQuotient

namespace AffineRootSystem

variable {V : Type v₁} {A : Type w₁} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
variable {W : Type v₂} {B : Type w₂} [AddCommGroup W] [Module ℝ W] [AddTorsor W B]
variable {X : Type u} {C : Type u} [AddCommGroup X] [Module ℝ X] [AddTorsor X C]

/-- Transport of roots along a composite affine equivalence. -/
theorem transportedRoots_trans (a : A ≃ᵃ[ℝ] B) (b : B ≃ᵃ[ℝ] C) (Ψ : Set (A →ᵃ[ℝ] ℝ)) :
    transportedRoots (a.trans b) Ψ = transportedRoots b (transportedRoots a Ψ) := by
  simp only [transportedRoots, Set.image_image]
  congr 1

/-- An affine automorphism stabilizing a root set transports it to itself. -/
theorem transportedRoots_eq_of_mem_rootStabilizer_algebraic {Ψ : Set (A →ᵃ[ℝ] ℝ)} {e : A ≃ᵃ[ℝ] A}
    (he : e ∈ rootStabilizer Ψ) : transportedRoots e Ψ = Ψ := by
  have he' : e⁻¹ ∈ rootStabilizer Ψ := inv_mem he
  ext ψ
  constructor
  · rintro ⟨ζ, hζ, rfl⟩
    exact (he' ζ).2 hζ
  · intro hψ
    refine ⟨ψ.comp (e : A →ᵃ[ℝ] A), (he ψ).2 hψ, ?_⟩
    ext x
    simp [affineFunctionalTransport_apply]

end AffineRootSystem

namespace KPApartmentData

variable {k : Type u} [Field k] {ω : kˣ → ℝ}
  {S₁ S₂ S₃ : CommGroupScheme (Spec (CommRingCat.of k))}
  {G₁ G₂ G₃ : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G₁.X.hom] [IsAffineHom G₂.X.hom] [IsAffineHom G₃.X.hom]
  {i₁ : S₁.toGrp ⟶ G₁} {i₂ : S₂.toGrp ⟶ G₂} {i₃ : S₃.toGrp ⟶ G₃}
  [Mono i₁.hom.hom.left] [Mono i₂.hom.hom.left] [Mono i₃.hom.hom.left]

/-- A comparison of the apartment class `D₁` of `(G₁, S₁)` with the apartment class `D₂` of
`(G₂, S₂)` along a homomorphism `θ : G₁(k) →* G₂(k)`: an affine equivalence `e` of the
apartments, intertwining the normalizer actions through `θ`, such that `θ` maps each
`G₁(k)^♯_x` onto `G₂(k)^♯_{e x}` and `e` transports the affine roots of `D₁` onto those of
`D₂`. -/
structure Comparison (D₁ : KPApartmentData i₁ ω) (D₂ : KPApartmentData i₂ ω)
    (θ : rationalPoints G₁ →* rationalPoints G₂) where
  /-- The affine comparison of the apartments. -/
  e : D₁.Apartment ≃ᵃ[ℝ] D₂.Apartment
  map_mem_normalizerPoints : ∀ n : normalizerPoints i₁, θ n ∈ normalizerPoints i₂
  e_smul : ∀ (n : normalizerPoints i₁) (x : D₁.Apartment),
    e (n • x) = (⟨θ n, map_mem_normalizerPoints n⟩ : normalizerPoints i₂) • e x
  map_sharpFixer : ∀ x : D₁.Apartment, (D₁.sharpFixer {x}).map θ = D₂.sharpFixer {e x}
  transportedRoots_eq : AffineRootSystem.transportedRoots e D₁.affineRoots = D₂.affineRoots

/-- A transfer of `D₁` to `D₂` along `θ`: a comparison such that moreover `θ` pulls `N₂(k)`
back into `N₁(k)` and `G₂(k) = θ(G₁(k)) · N₂(k)`. -/
structure Transfer (D₁ : KPApartmentData i₁ ω) (D₂ : KPApartmentData i₂ ω)
    (θ : rationalPoints G₁ →* rationalPoints G₂) extends Comparison D₁ D₂ θ where
  mem_normalizerPoints_of_map :
    ∀ g : rationalPoints G₁, θ g ∈ normalizerPoints i₂ → g ∈ normalizerPoints i₁
  exists_mul : ∀ h : rationalPoints G₂, ∃ (g : rationalPoints G₁) (n : normalizerPoints i₂),
    h = θ g * n

namespace Comparison

variable {D₁ : KPApartmentData i₁ ω} {D₂ : KPApartmentData i₂ ω} {D₃ : KPApartmentData i₃ ω}
  {θ : rationalPoints G₁ →* rationalPoints G₂} {θ' : rationalPoints G₂ →* rationalPoints G₃}

/-- The identity comparison. -/
def refl (D : KPApartmentData i₁ ω) : Comparison D D (MonoidHom.id _) where
  e := AffineEquiv.refl ℝ _
  map_mem_normalizerPoints n := n.2
  e_smul _ _ := rfl
  map_sharpFixer x := Subgroup.map_id _
  transportedRoots_eq := by
    ext ψ
    constructor
    · rintro ⟨ζ, hζ, rfl⟩
      exact hζ
    · intro hψ
      exact ⟨ψ, hψ, rfl⟩

/-- Comparisons compose. -/
def trans (t : Comparison D₁ D₂ θ) (t' : Comparison D₂ D₃ θ') :
    Comparison D₁ D₃ (θ'.comp θ) where
  e := t.e.trans t'.e
  map_mem_normalizerPoints n :=
    t'.map_mem_normalizerPoints ⟨θ n, t.map_mem_normalizerPoints n⟩
  e_smul n x := by
    rw [AffineEquiv.trans_apply, t.e_smul, t'.e_smul]
    rfl
  map_sharpFixer x := by
    rw [← Subgroup.map_map, t.map_sharpFixer, t'.map_sharpFixer]
    rfl
  transportedRoots_eq := by
    rw [AffineRootSystem.transportedRoots_trans, t.transportedRoots_eq, t'.transportedRoots_eq]

theorem trans_e (t : Comparison D₁ D₂ θ) (t' : Comparison D₂ D₃ θ') (x : D₁.Apartment) :
    (t.trans t').e x = t'.e (t.e x) :=
  rfl

/-- Replace the homomorphism of a comparison by an equal one. -/
def congrHom {θ₀ : rationalPoints G₁ →* rationalPoints G₂} (t : Comparison D₁ D₂ θ)
    (hθ : θ = θ₀) : Comparison D₁ D₂ θ₀ :=
  hθ ▸ t

theorem congrHom_e {θ₀ : rationalPoints G₁ →* rationalPoints G₂} (t : Comparison D₁ D₂ θ)
    (hθ : θ = θ₀) : (t.congrHom hθ).e = t.e := by
  subst hθ
  rfl

/-- Replace the source apartment class of a comparison by an equal one. -/
def congrLeft {D₁' : KPApartmentData i₁ ω} (t : Comparison D₁ D₂ θ) (hD : D₁' = D₁) :
    Comparison D₁' D₂ θ :=
  hD ▸ t

theorem congrLeft_linear {D₁' : KPApartmentData i₁ ω} (t : Comparison D₁ D₂ θ)
    (hD : D₁' = D₁) : (t.congrLeft hD).e.linear = t.e.linear := by
  subst hD
  rfl

/-- The inverse of `e` intertwines the normalizer actions through `θ`. -/
theorem e_symm_smul (t : Comparison D₁ D₂ θ) (n : normalizerPoints i₁) (x : D₂.Apartment) :
    t.e.symm ((⟨θ n, t.map_mem_normalizerPoints n⟩ : normalizerPoints i₂) • x) =
      n • t.e.symm x := by
  apply t.e.injective
  rw [AffineEquiv.apply_symm_apply, t.e_smul, AffineEquiv.apply_symm_apply]

end Comparison

namespace Transfer

variable {D₁ : KPApartmentData i₁ ω} {D₂ : KPApartmentData i₂ ω} {D₃ : KPApartmentData i₃ ω}
  {θ : rationalPoints G₁ →* rationalPoints G₂} {θ' : rationalPoints G₂ →* rationalPoints G₃}

/-- The identity transfer. -/
def refl (D : KPApartmentData i₁ ω) : Transfer D D (MonoidHom.id _) where
  toComparison := Comparison.refl D
  mem_normalizerPoints_of_map _ hg := hg
  exists_mul h := ⟨h, 1, by simp⟩

/-- Transfers compose. -/
def trans (t : Transfer D₁ D₂ θ) (t' : Transfer D₂ D₃ θ') : Transfer D₁ D₃ (θ'.comp θ) where
  toComparison := t.toComparison.trans t'.toComparison
  mem_normalizerPoints_of_map g hg :=
    t.mem_normalizerPoints_of_map g (t'.mem_normalizerPoints_of_map _ hg)
  exists_mul h := by
    obtain ⟨g₂, n₂, rfl⟩ := t'.exists_mul h
    obtain ⟨g₁, n₁, rfl⟩ := t.exists_mul g₂
    refine ⟨g₁, ⟨θ' n₁, t'.map_mem_normalizerPoints n₁⟩ * n₂, ?_⟩
    simp only [map_mul, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_mul, mul_assoc]

theorem trans_e (t : Transfer D₁ D₂ θ) (t' : Transfer D₂ D₃ θ') (x : D₁.Apartment) :
    (t.trans t').e x = t'.e (t.e x) :=
  rfl

/-- The quotient hypotheses for the sharp-fixer families. -/
theorem isHomComparison (t : Transfer D₁ D₂ θ) :
    ApartmentQuotient.IsHomComparison D₁.sharpFixerFamily D₂.sharpFixerFamily θ
      t.e.toEquiv where
  map_mem := t.map_mem_normalizerPoints
  map_smul := t.e_smul
  map_family := t.map_sharpFixer
  mem_of_map_mem := t.mem_normalizerPoints_of_map
  exists_mul := t.exists_mul

/-- The induced bijection of reduced buildings, `[(g, x)] ↦ [(θ g, e x)]`. -/
def reducedBuildingEquiv (t : Transfer D₁ D₂ θ) : D₁.ReducedBuilding ≃ D₂.ReducedBuilding :=
  ApartmentQuotient.homEquiv t.isHomComparison

theorem reducedBuildingEquiv_mk (t : Transfer D₁ D₂ θ) (g : rationalPoints G₁)
    (x : D₁.Apartment) :
    t.reducedBuildingEquiv (ApartmentQuotient.mk D₁.sharpFixerFamily (g, x)) =
      ApartmentQuotient.mk D₂.sharpFixerFamily (θ g, t.e x) :=
  rfl

theorem reducedBuildingEquiv_apartmentMap (t : Transfer D₁ D₂ θ) (x : D₁.Apartment) :
    t.reducedBuildingEquiv (D₁.apartmentMap x) = D₂.apartmentMap (t.e x) :=
  ApartmentQuotient.homMap_apartment t.isHomComparison x

theorem reducedBuildingEquiv_smul (t : Transfer D₁ D₂ θ) (g : rationalPoints G₁)
    (q : D₁.ReducedBuilding) :
    t.reducedBuildingEquiv (g • q) = θ g • t.reducedBuildingEquiv q :=
  ApartmentQuotient.homMap_smul t.isHomComparison g q

end Transfer

end KPApartmentData

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G₁ G₂ : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G₁.X.hom] [IsAffineHom G₂.X.hom]
  {B₁ : ValuationBuildingData G₁} {B₂ : ValuationBuildingData G₂}
  {θ : rationalPoints G₁ →* rationalPoints G₂}

/-- The normalizer acts on the apartment by affine automorphisms preserving the affine
roots, so it permutes the apartment facets. -/
theorem isFacet_normalizer_image_iff (B : ValuationBuildingData G₁) (n : normalizerPoints B.i)
    (Fa : Set B.Apartment) :
    AffineRootSystem.IsFacet B.affineRoots (B.apartment.normalizerAffineEquiv n '' Fa) ↔
      AffineRootSystem.IsFacet B.affineRoots Fa :=
  AffineRootSystem.isFacet_image_iff_of_transportedRoots_eq _
    (AffineRootSystem.transportedRoots_eq_of_mem_rootStabilizer_algebraic
      (B.apartment.normalizerAffineEquiv_mem_rootStabilizer n)) Fa

namespace TransferIso

variable (t : B₁.apartment.Transfer B₂.apartment θ)

theorem translatedApartmentMap (g : rationalPoints G₁) (x : B₁.Apartment) :
    t.reducedBuildingEquiv (B₁.translatedApartmentMap g x) =
      B₂.translatedApartmentMap (θ g) (t.e x) := by
  change t.reducedBuildingEquiv (g • B₁.apartmentMap x) = θ g • B₂.apartmentMap (t.e x)
  rw [t.reducedBuildingEquiv_smul]
  congr 1
  exact t.reducedBuildingEquiv_apartmentMap x

theorem image_translatedApartmentMap (g : rationalPoints G₁) (Fa : Set B₁.Apartment) :
    t.reducedBuildingEquiv '' (B₁.translatedApartmentMap g '' Fa) =
      B₂.translatedApartmentMap (θ g) '' (t.e '' Fa) := by
  rw [Set.image_image, Set.image_image]
  congr 1
  funext x
  exact translatedApartmentMap t g x

theorem image_apartment (g : rationalPoints G₁) :
    t.reducedBuildingEquiv '' (g • B₁.apartmentImage) = θ g • B₂.apartmentImage := by
  rw [← B₁.range_translatedApartmentMap, ← B₂.range_translatedApartmentMap,
    ← Set.image_univ, image_translatedApartmentMap, Set.image_univ_of_surjective t.e.surjective,
    Set.image_univ]

theorem isApartment_image_iff (Y : Set B₁.ReducedBuilding) :
    B₂.IsApartment (t.reducedBuildingEquiv '' Y) ↔ B₁.IsApartment Y := by
  constructor
  · rintro ⟨g', hg'⟩
    obtain ⟨g, n, rfl⟩ := t.exists_mul g'
    refine ⟨g, t.reducedBuildingEquiv.injective.image_injective ?_⟩
    rw [image_apartment, hg', mul_smul]
    congr 1
    exact B₂.normalizerPoints_le_stabilizer_apartmentImage n.2
  · rintro ⟨g, rfl⟩
    exact ⟨θ g, image_apartment t g⟩

theorem isFacet_image_iff (Y : Set B₁.ReducedBuilding) :
    B₂.IsFacet (t.reducedBuildingEquiv '' Y) ↔ B₁.IsFacet Y := by
  constructor
  · rintro ⟨g', Fa₂, hFa₂, hY⟩
    obtain ⟨g, n, rfl⟩ := t.exists_mul g'
    set Fa₂' := B₂.apartment.normalizerAffineEquiv n '' Fa₂ with hFa₂'
    have hF' : AffineRootSystem.IsFacet B₂.affineRoots Fa₂' :=
      (isFacet_normalizer_image_iff B₂ n Fa₂).2 hFa₂
    have himage : t.e '' (t.e.symm '' Fa₂') = Fa₂' := t.e.toEquiv.image_symm_image Fa₂'
    have hFa₁ : AffineRootSystem.IsFacet B₁.affineRoots (t.e.symm '' Fa₂') := by
      apply (AffineRootSystem.isFacet_image_iff_of_transportedRoots_eq t.e
        t.transportedRoots_eq _).1
      rwa [himage]
    refine ⟨g, t.e.symm '' Fa₂', hFa₁, t.reducedBuildingEquiv.injective.image_injective ?_⟩
    change t.reducedBuildingEquiv '' Y =
      t.reducedBuildingEquiv '' (B₁.translatedApartmentMap g '' (t.e.symm '' Fa₂'))
    rw [image_translatedApartmentMap, himage, hY, hFa₂', Set.image_image]
    congr 1
    funext x
    change (θ g * n) • B₂.apartmentMap x = θ g • B₂.apartmentMap (n • x)
    rw [mul_smul, B₂.normalizer_smul_apartmentMap]
  · rintro ⟨g, Fa₁, hFa₁, rfl⟩
    refine ⟨θ g, t.e '' Fa₁,
      (AffineRootSystem.isFacet_image_iff_of_transportedRoots_eq t.e t.transportedRoots_eq _).2
        hFa₁, ?_⟩
    exact image_translatedApartmentMap t g Fa₁

end TransferIso

/-- A transfer of apartment classes along `θ` gives an equivariant isomorphism of reduced
buildings along `θ`. -/
theorem Transfer.isEquivariantBuildingIso (t : B₁.apartment.Transfer B₂.apartment θ) :
    IsEquivariantBuildingIso B₁ B₂ θ t.reducedBuildingEquiv :=
  ⟨{ isFacet_image_iff := TransferIso.isFacet_image_iff t
     isApartment_image_iff := TransferIso.isApartment_image_iff t
     exists_affineEquiv := fun g => ⟨θ g, t.e, TransferIso.translatedApartmentMap t g⟩ },
    t.reducedBuildingEquiv_smul⟩

/-- A transfer of apartment classes along `θ` gives an equivariant building isomorphism. -/
theorem exists_isEquivariantBuildingIso_of_transfer
    (t : B₁.apartment.Transfer B₂.apartment θ) :
    ∃ Φ : B₁.ReducedBuilding ≃ B₂.ReducedBuilding, IsEquivariantBuildingIso B₁ B₂ θ Φ :=
  ⟨t.reducedBuildingEquiv, Transfer.isEquivariantBuildingIso t⟩

end ValuationBuildingData

end Langlands.Geometry.Building
