import Langlands.Geometry.Building.FullValidity.AffineApartment
import Langlands.Geometry.Building.FullValidity.ChamberAxioms
import Langlands.BruhatTits.IntegralModels.FacetAxioms
import Langlands.GroupScheme.IntegralModel.LocalField
import Langlands.GroupScheme.Adjoint.Quotient
import Langlands.GroupScheme.SimplyConnected.DerivedCover

/-!
# The full corrected Definition 4.1.26: availability of Bruhat–Tits theory

KP Definition 4.1.26, as corrected in 2024, says that Bruhat–Tits theory is available for `G`
over `k` if Axioms 4.1.1, 4.1.2, 4.1.4, 4.1.6, 4.1.8, 4.1.9, 4.1.16, 4.1.17, 4.1.20 and 4.1.22
hold. This module assembles these ten axioms on actual building and integral-model data.

* `KPBuildingDatum G`: supplied data for one group `G` over a nonarchimedean local field `F`.
  These are the Library's parahoric building data `base` (reduced building `B(G)`, apartment
  `A(S)`, root groups, valuations, `G(F)^0`, `Z(F)^0`), a polysimplicial structure on `B(G)`, the
  derived and central tori of Axiom 4.1.4, a subset-indexed family of integral models with their
  morphisms and split tori (Axiom 4.1.20), the radicals and quotients of their special fibres
  (Axiom 4.1.22), and relative coroots with reflection representatives.
* `KPBuildingDatum.SatisfiesGroupAxioms D`: the clauses of the ten axioms that concern `G`
  alone. This is not full validity: the comparisons of Axiom 4.1.1 between groups and Axiom
  4.1.17 are missing.
* `KPBuildingAssignment`: a choice of such data for every connected reductive group over every
  nonarchimedean local field in universe `u`.
* `KPBuildingAssignment.IsAvailableFor 𝔅 F G hG`: KP Definition 4.1.26 for `G` over `F`, with
  one field for each of the ten axioms. Axiom 4.1.1 contains the comparisons for surjective
  homomorphisms with central kernel out of `G` and the identifications with the buildings of the
  derived subgroup and of its simply connected cover. Axiom 4.1.17 covers every valued-field
  isomorphism out of `F` and every isomorphism of `G` with a group over the target field.
* `KPBuildingAssignment.IsValid 𝔅`: availability for every group.

The adapter `IsAvailableFor.satisfiesPartialBuildingAxioms` projects to the Library's partial
bundle `ParahoricBuildingData.SatisfiesPartialBuildingAxioms` on the same data. Nothing here
asserts that any of these predicates holds, or that data or an assignment exist.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel

namespace Langlands.Geometry.Building

open BruhatTits.IntegralModels

/-! ### Surjective homomorphisms with central kernel and isomorphisms of valued fields -/

section GroupMaps

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- A homomorphism `f : G → H` that is surjective (on the underlying schemes) and whose actual
kernel is central in `G`: the maps of the comparison clause of KP Axiom 4.1.1. -/
structure IsCentralSurjection (f : G ⟶ H) : Prop where
  /-- `f` is surjective. -/
  surjective : Surjective f.hom.hom.left
  /-- The kernel of `f` is central. -/
  isCentral_kernelι : IsCentral (kernelι f)

/-- An actual adjoint quotient `G → G_ad` is surjective with central kernel. -/
theorem isCentralSurjection_of_isAdjointQuotient {q : G ⟶ H} (hq : IsAdjointQuotient q) :
    IsCentralSurjection q :=
  ⟨hq.surjective, hq.kernelCenter.isCentral⟩

/-- A central isogeny is surjective with central kernel. -/
theorem isCentralSurjection_of_isCentralIsogeny {f : G ⟶ H} (hf : IsCentralIsogeny f) :
    IsCentralSurjection f :=
  ⟨hf.surjective, hf.isCentral_kernelι⟩

end GroupMaps

section FieldIsomorphisms

variable {F₁ F₂ : Type u} [Field F₁] [Field F₂]

/-- `σ : F₁ ≃+* F₂` is an isomorphism of valued fields: it identifies the valuative relations. -/
def IsValuativeRingEquiv [ValuativeRel F₁] [ValuativeRel F₂] (σ : F₁ ≃+* F₂) : Prop :=
  ∀ a b : F₁, σ a ≤ᵥ σ b ↔ a ≤ᵥ b

/-- The morphism `Spec F₂ → Spec F₁` induced by `σ : F₁ ≃+* F₂`. -/
abbrev specMapOfRingEquiv (σ : F₁ ≃+* F₂) :
    Spec (CommRingCat.of F₂) ⟶ Spec (CommRingCat.of F₁) :=
  Spec.map (CommRingCat.ofHom σ.toRingHom)

/-- For `f_G : G₁ ×_{F₁,σ} F₂ → G₂`, the map `g₁ ↦ f_G(g₁)` from `G₁(F₁)` to `G₂(F₂)`: the
`F₁`-point `g₁` gives an `F₂`-point of the base change, and `f_G` maps it to `G₂`. -/
def coveringPointsMap (σ : F₁ ≃+* F₂) {G₁ : GroupScheme (Spec (CommRingCat.of F₁))}
    {G₂ : GroupScheme (Spec (CommRingCat.of F₂))}
    (fG : (GroupScheme.baseChange (specMapOfRingEquiv σ)).obj G₁ ⟶ G₂) :
    rationalPoints G₁ →* rationalPoints G₂ :=
  (rationalPoints.map fG).comp (baseChangeSectionHom (specMapOfRingEquiv σ) G₁)

theorem coveringPointsMap_apply (σ : F₁ ≃+* F₂) {G₁ : GroupScheme (Spec (CommRingCat.of F₁))}
    {G₂ : GroupScheme (Spec (CommRingCat.of F₂))}
    (fG : (GroupScheme.baseChange (specMapOfRingEquiv σ)).obj G₁ ⟶ G₂) (g : rationalPoints G₁) :
    coveringPointsMap σ fG g =
      rationalPoints.map fG (baseChangeSectionHom (specMapOfRingEquiv σ) G₁ g) :=
  rfl

end FieldIsomorphisms

/-! ### Isomorphisms of buildings -/

namespace ValuationBuildingData

section Isomorphisms

variable {F₁ F₂ F₃ : Type u} [Field F₁] [ValuativeRel F₁] [TopologicalSpace F₁]
  [IsNonarchimedeanLocalField F₁] [Field F₂] [ValuativeRel F₂] [TopologicalSpace F₂]
  [IsNonarchimedeanLocalField F₂] [Field F₃] [ValuativeRel F₃] [TopologicalSpace F₃]
  [IsNonarchimedeanLocalField F₃]
  {G₁ : GroupScheme (Spec (CommRingCat.of F₁))} [IsAffineHom G₁.X.hom]
  {G₂ : GroupScheme (Spec (CommRingCat.of F₂))} [IsAffineHom G₂.X.hom]
  {G₃ : GroupScheme (Spec (CommRingCat.of F₃))} [IsAffineHom G₃.X.hom]

/-- `Φ : B(G₁) → B(G₂)` is an isomorphism of buildings: it maps facets onto facets and
apartments onto apartments (a building is a polysimplicial complex together with its apartments,
KP Definitions 1.5.1(13) and 1.5.5, §7.10), and on every apartment it is affine (the geometric
realization, whose apartments carry the affine structure of Axiom 4.1.4): in the charts
`x ↦ g₁ · x` and `x ↦ g₂ · x` it is an affine isomorphism `A(S₁) → A(S₂)`. -/
structure IsBuildingIso (B₁ : ValuationBuildingData G₁) (B₂ : ValuationBuildingData G₂)
    (Φ : B₁.ReducedBuilding ≃ B₂.ReducedBuilding) : Prop where
  /-- `Φ` maps facets to facets, and only facets to facets. -/
  isFacet_image_iff : ∀ Y : Set B₁.ReducedBuilding, B₂.IsFacet (Φ '' Y) ↔ B₁.IsFacet Y
  /-- `Φ` maps apartments to apartments, and only apartments to apartments. -/
  isApartment_image_iff : ∀ Y : Set B₁.ReducedBuilding,
    B₂.IsApartment (Φ '' Y) ↔ B₁.IsApartment Y
  /-- `Φ` is affine on every apartment `g₁ · A(S₁)`. -/
  exists_affineEquiv : ∀ g₁ : rationalPoints G₁, ∃ (g₂ : rationalPoints G₂)
    (f : B₁.Apartment ≃ᵃ[ℝ] B₂.Apartment),
      ∀ x, Φ (B₁.translatedApartmentMap g₁ x) = B₂.translatedApartmentMap g₂ (f x)

/-- `Φ : B(G₁) → B(G₂)` is an isomorphism of buildings with `Φ(g · y) = φ(g) · Φ(y)` for
`g ∈ G₁(F₁)`. -/
def IsEquivariantBuildingIso (B₁ : ValuationBuildingData G₁) (B₂ : ValuationBuildingData G₂)
    (φ : rationalPoints G₁ →* rationalPoints G₂) (Φ : B₁.ReducedBuilding ≃ B₂.ReducedBuilding) :
    Prop :=
  IsBuildingIso B₁ B₂ Φ ∧ ∀ (g : rationalPoints G₁) (y : B₁.ReducedBuilding), Φ (g • y) = φ g • Φ y

/-- The identity is an isomorphism of buildings. -/
theorem isBuildingIso_refl (B : ValuationBuildingData G₁) : IsBuildingIso B B (Equiv.refl _) where
  isFacet_image_iff Y := by rw [Equiv.coe_refl, Set.image_id]
  isApartment_image_iff Y := by rw [Equiv.coe_refl, Set.image_id]
  exists_affineEquiv g := ⟨g, AffineEquiv.refl ℝ _, fun _ => rfl⟩

/-- The composite of isomorphisms of buildings is an isomorphism of buildings. -/
theorem IsBuildingIso.trans {B₁ : ValuationBuildingData G₁} {B₂ : ValuationBuildingData G₂}
    {B₃ : ValuationBuildingData G₃} {Φ : B₁.ReducedBuilding ≃ B₂.ReducedBuilding}
    {Ψ : B₂.ReducedBuilding ≃ B₃.ReducedBuilding} (h₁ : IsBuildingIso B₁ B₂ Φ)
    (h₂ : IsBuildingIso B₂ B₃ Ψ) : IsBuildingIso B₁ B₃ (Φ.trans Ψ) where
  isFacet_image_iff Y := by
    rw [Equiv.coe_trans, Set.image_comp, h₂.isFacet_image_iff, h₁.isFacet_image_iff]
  isApartment_image_iff Y := by
    rw [Equiv.coe_trans, Set.image_comp, h₂.isApartment_image_iff, h₁.isApartment_image_iff]
  exists_affineEquiv g₁ := by
    obtain ⟨g₂, f₁, hf₁⟩ := h₁.exists_affineEquiv g₁
    obtain ⟨g₃, f₂, hf₂⟩ := h₂.exists_affineEquiv g₂
    exact ⟨g₃, f₁.trans f₂, fun x => by rw [Equiv.trans_apply, hf₁, hf₂]; rfl⟩

/-- The identity is an equivariant isomorphism of buildings along the identity of `G(F)`. -/
theorem isEquivariantBuildingIso_refl (B : ValuationBuildingData G₁) :
    IsEquivariantBuildingIso B B (MonoidHom.id _) (Equiv.refl _) :=
  ⟨isBuildingIso_refl B, fun _ _ => rfl⟩

/-- Equivariant isomorphisms of buildings compose along the composite of the group maps. -/
theorem IsEquivariantBuildingIso.trans {B₁ : ValuationBuildingData G₁}
    {B₂ : ValuationBuildingData G₂} {B₃ : ValuationBuildingData G₃}
    {φ : rationalPoints G₁ →* rationalPoints G₂} {ψ : rationalPoints G₂ →* rationalPoints G₃}
    {Φ : B₁.ReducedBuilding ≃ B₂.ReducedBuilding} {Ψ : B₂.ReducedBuilding ≃ B₃.ReducedBuilding}
    (h₁ : IsEquivariantBuildingIso B₁ B₂ φ Φ) (h₂ : IsEquivariantBuildingIso B₂ B₃ ψ Ψ) :
    IsEquivariantBuildingIso B₁ B₃ (ψ.comp φ) (Φ.trans Ψ) :=
  ⟨h₁.1.trans h₂.1, fun g y => by
    rw [Equiv.trans_apply, h₁.2, h₂.2, Equiv.trans_apply, MonoidHom.comp_apply]⟩

end Isomorphisms

/-! ### Axiom 4.1.8 (1) -/

section HalfApartments

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- KP Axiom 4.1.8 (1): for `ψ ∈ Ψ` with derivative the root `a`, the group `U_ψ` fixes the
half-apartment `A_{ψ ≥ 0}` of `A(S)` pointwise in `B(G)`. It holds for every `B`
(`hasHalfApartmentFixers`). -/
def HasHalfApartmentFixers : Prop :=
  ∀ (α : relativeRoots B.i) (ψ : B.Apartment →ᵃ[ℝ] ℝ), ψ ∈ B.affineRoots →
    ψ.linear = rootForm B.i α →
      B.affineRootGroup α ψ ≤ B.pointwiseFixer (B.apartmentMap '' {x | 0 ≤ ψ x})

/-- Axiom 4.1.8 (1) holds for all building data, by the Library's
`affineRootGroup_le_pointwiseFixer` (KP Fact 7.6.7). -/
theorem hasHalfApartmentFixers : B.HasHalfApartmentFixers :=
  fun _ _ _ hψ => B.affineRootGroup_le_pointwiseFixer hψ

end HalfApartments

end ValuationBuildingData

/-! ### Comparisons of fixers -/

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- The pointwise fixer `G(F)^0_Ω` (`zeroFixer`, KP §4.1 before Axiom 4.1.8) lies in the
stabilizer `G(F)^0_Ω` of the set `Ω` (`zeroStabilizer`, KP Definition 4.1.3). -/
theorem zeroFixer_le_zeroStabilizer (Ω : Set P.Apartment) :
    P.zeroFixer Ω ≤ P.zeroStabilizer (P.apartmentMap '' Ω) := by
  intro g hg
  rw [mem_zeroFixer] at hg
  refine ⟨hg.1, ?_⟩
  change g • (P.apartmentMap '' Ω) = P.apartmentMap '' Ω
  ext y
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (hg.2 x hx).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, hg.2 x hx⟩

/-- The zero fixer of the model family of Axiom 4.1.20 at a subset `Ω` of `A(S)` (pointwise
fixer of the image of `Ω` in `G(F)^0`) is the zero fixer `P.zeroFixer Ω` of Axiom 4.1.8. -/
theorem modelZeroFixer_ofApartment_one (Ω : Set P.Apartment) (hne : Ω.Nonempty)
    (hb : P.IsBoundedSubset Ω) :
    BuildingModelFamily.zeroFixer P (BuildingModelIndex.ofApartment 1 Ω hne hb) =
      P.zeroFixer Ω := by
  rw [BuildingModelFamily.zeroFixer, zeroFixer, inf_comm]
  congr 2
  ext y
  simp [BuildingModelIndex.ofApartment]

end ParahoricBuildingData

/-! ### Supplied data for one group -/

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Supplied data for the Bruhat–Tits theory of `G` over `F` in the sense of KP §4.1:

* `base`: the Library's parahoric building data, with the reduced building `B(G)`, the maximal
  split torus `S`, the apartment `A(S)`, the root groups and valuations, `Z(F)^0` and `G(F)^0`;
* `realization`: a polysimplicial complex whose facets are the facets of `B(G)` (Axiom 4.1.1);
* `splitting`: the derived subgroup, its torus `S'` and the split central torus `A_G`
  (Axiom 4.1.4);
* `models`: integral models over `𝒪[F]` for the nonempty bounded subsets of the apartments and
  the facets of `B(G)`, with their morphisms and split integral tori (Axioms 4.1.20, 4.1.22);
* `quotients`: unipotent radicals and reductive quotients of the special fibres of the facet
  models (Axiom 4.1.22);
* `rootDatum`: coroots and reflection representatives of the relative roots (the root datum of
  Axiom 4.1.22 (6)).

These are data only; the validity clauses are in `SatisfiesGroupAxioms` and
`KPBuildingAssignment.IsAvailableFor`. -/
structure KPBuildingDatum (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom] where
  /-- The building, apartment, root-group and zero-subgroup data. -/
  base : ParahoricBuildingData G
  /-- The polysimplicial structure on `B(G)`. -/
  realization : base.toValuationBuildingData.PolysimplicialRealization
  /-- The tori `S'` and `A_G` of Axiom 4.1.4. -/
  splitting : base.toValuationBuildingData.ApartmentSplitting
  /-- The integral models of Axiom 4.1.20 and their morphisms. -/
  models : BuildingModelFamily base.toValuationBuildingData ↥𝒪[F]
  /-- The radicals and reductive quotients of Axiom 4.1.22. -/
  quotients : BuildingModelQuotientFamily base.toValuationBuildingData models
  /-- Coroots and reflection representatives of the relative roots. -/
  rootDatum : RelativeRootReflectionData base.i

namespace KPBuildingDatum

variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] (D : KPBuildingDatum G)

/-- KP Axiom 4.1.6 (AS 1–AS 6) on the apartment `A(S)` of `D`:

* AS 1: `m(u)` fixes the hyperplane `H_u` (`rootReflections`);
* AS 2–AS 5, including both inclusions and both equalities of AS 5, together with V 7 of the
  valuations (`apartmentAxioms`, the Library's `SatisfiesApartmentAxioms`);
* AS 6: the facets of `A(S)` for `Ψ` are those of `B(G)` (`compatibleApartmentFacets`). -/
structure SatisfiesAffineRootSystemAxiom : Prop where
  /-- AS 1. -/
  rootReflections : D.base.HasRootReflections
  /-- V 7 and AS 2–AS 5. -/
  apartmentAxioms : D.base.SatisfiesApartmentAxioms
  /-- AS 6. -/
  compatibleApartmentFacets : D.base.HasCompatibleApartmentFacets

/-- KP Axiom 4.1.8 on the apartment `A(S)` of `D`, with the corrected hypothesis that `Ω` is
non-empty and bounded in (2) and (3). -/
structure SatisfiesRootGroupActionAxiom : Prop where
  /-- (1): `U_ψ` fixes `A_{ψ ≥ 0}` pointwise. -/
  halfApartmentFixers : D.base.HasHalfApartmentFixers
  /-- (2): `G(F)^0_Ω` is generated by `Z(F)^0` and the `U_ψ` with `ψ(Ω) ≥ 0`. -/
  zeroFixerGenerators : D.base.HasZeroFixerGenerators
  /-- (3): `U_a(F) ∩ G(F)^0_Ω = U_ψ` for the smallest `ψ ∈ Ψ′` non-negative on `Ω`. -/
  rootZeroFixers : D.base.HasRootZeroFixers

/-- Axiom 4.1.8 (1) holds for all data. -/
theorem satisfiesRootGroupActionAxiom_iff :
    D.SatisfiesRootGroupActionAxiom ↔
      D.base.HasZeroFixerGenerators ∧ D.base.HasRootZeroFixers :=
  ⟨fun h => ⟨h.zeroFixerGenerators, h.rootZeroFixers⟩,
    fun h => ⟨D.base.hasHalfApartmentFixers, h.1, h.2⟩⟩

/-- The clauses of the ten axioms of KP Definition 4.1.26 that concern the group `G` alone: the
one-group part of Axiom 4.1.1 and Axioms 4.1.2, 4.1.4, 4.1.6, 4.1.8, 4.1.9, 4.1.16, 4.1.20 and
4.1.22. The comparisons between groups in Axiom 4.1.1 and Axiom 4.1.17 are not included; full
validity is `KPBuildingAssignment.IsAvailableFor`. -/
structure SatisfiesGroupAxioms : Prop where
  /-- Axiom 4.1.1 for `G`: the building, its action, apartments and tori, stabilizers. -/
  building : D.base.SatisfiesBuildingAxiom D.realization
  /-- Axiom 4.1.2: the `G(F)^1_y` are bounded open subgroups. -/
  boundedSubgroups : D.base.HasBoundedOpenStabilizers
  /-- Axiom 4.1.4: A 0, A 1 and A 2. -/
  affineStructure : D.base.SatisfiesAffineApartmentAxiom D.splitting
  /-- Axiom 4.1.6: AS 1–AS 6. -/
  affineRootSystem : D.SatisfiesAffineRootSystemAxiom
  /-- Axiom 4.1.8 (1)–(3). -/
  rootGroupAction : D.SatisfiesRootGroupActionAxiom
  /-- Axiom 4.1.9 as corrected. -/
  titsSystem : D.base.HasTitsSystem
  /-- Axiom 4.1.16. -/
  iwahoriDecomposition : D.base.HasIwahoriDecomposition
  /-- Axiom 4.1.20. -/
  bruhatTitsGroupSchemes : D.models.SatisfiesModelAxioms D.base
  /-- Axiom 4.1.22. -/
  reductiveQuotients : D.quotients.SatisfiesMorphismAxioms D.rootDatum

variable {D}

/-- Projection to the Library's partial bundle on the same parahoric building data. -/
theorem SatisfiesGroupAxioms.satisfiesPartialBuildingAxioms (h : D.SatisfiesGroupAxioms) :
    D.base.SatisfiesPartialBuildingAxioms where
  apartmentAxioms := h.affineRootSystem.apartmentAxioms
  hasRootReflections := h.affineRootSystem.rootReflections
  hasCompatibleApartmentFacets := h.affineRootSystem.compatibleApartmentFacets
  hasNormalizerApartmentStabilizer := h.building.normalizerApartmentStabilizer
  hasBoundedOpenStabilizers := h.boundedSubgroups
  hasZeroFixerGenerators := h.rootGroupAction.zeroFixerGenerators
  hasRootZeroFixers := h.rootGroupAction.rootZeroFixers

/-- The underlying partially valid parahoric building data. -/
def SatisfiesGroupAxioms.toPartiallyValidParahoricBuildingData (h : D.SatisfiesGroupAxioms) :
    PartiallyValidParahoricBuildingData G where
  toParahoricBuildingData := D.base
  satisfiesPartialBuildingAxioms := h.satisfiesPartialBuildingAxioms

@[simp] theorem SatisfiesGroupAxioms.toParahoricBuildingData_toPartiallyValid
    (h : D.SatisfiesGroupAxioms) :
    h.toPartiallyValidParahoricBuildingData.toParahoricBuildingData = D.base :=
  rfl

/-- Under Axiom 4.1.8 (2), `G(F)^0_Ω ⊆ P_Ω` for non-empty bounded `Ω ⊆ A(S)`: the pointwise zero
fixer lies in the Chapter 7 group `P.parahoric Ω`. Equality is not asserted. -/
theorem SatisfiesRootGroupActionAxiom.zeroFixer_le_parahoric
    (h : D.SatisfiesRootGroupActionAxiom) {Ω : Set D.base.Apartment} (hne : Ω.Nonempty)
    (hb : D.base.IsBoundedSubset Ω) : D.base.zeroFixer Ω ≤ D.base.parahoric Ω :=
  h.zeroFixerGenerators.zeroFixer_le_parahoric hne hb

end KPBuildingDatum

/-! ### Assignments for all groups -/

/-- A choice of data `KPBuildingDatum G` for every connected reductive group `G` over every
nonarchimedean local field `F` in universe `u`. Axioms 4.1.1 (comparisons) and 4.1.17 relate the
data of different groups and fields. -/
structure KPBuildingAssignment where
  /-- The data for `G` over `F`. -/
  datum : ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom], IsConnectedReductive G → KPBuildingDatum G

namespace KPBuildingAssignment

variable (𝔅 : KPBuildingAssignment.{u}) (F) (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] (hG : IsConnectedReductive G)

/-- The building data `B` of `G` in the assignment. -/
abbrev buildingData : ValuationBuildingData G :=
  (𝔅.datum F G hG).base.toValuationBuildingData

/-- The reduced building `B(G)` of `G` in the assignment. -/
abbrev building : Type u :=
  (𝔅.buildingData F G hG).ReducedBuilding

/-- The comparison clause of KP Axiom 4.1.1 for maps out of `G`: every surjective homomorphism
`f : G → G'` with central kernel to a connected reductive group induces an isomorphism of
buildings `B(G) → B(G')` with `Φ(g · y) = f(g) · Φ(y)`. -/
def HasCentralQuotientComparisons : Prop :=
  ∀ (G' : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G'.X.hom]
    (hG' : IsConnectedReductive G') (f : G ⟶ G'), IsCentralSurjection f →
      ∃ Φ : 𝔅.building F G hG ≃ 𝔅.building F G' hG',
        ValuationBuildingData.IsEquivariantBuildingIso (𝔅.buildingData F G hG)
          (𝔅.buildingData F G' hG') (rationalPoints.map f) Φ

/-- The identification of KP Axiom 4.1.1 of the building of the derived subgroup with `B(G)`:
for every actual derived subgroup `d : G_der → G`, an isomorphism of buildings
`B(G_der) → B(G)` with `Φ(h · y) = d(h) · Φ(y)`. -/
def HasDerivedSubgroupIdentification : Prop :=
  ∀ (Gder : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom Gder.X.hom]
    (hder : IsConnectedReductive Gder) (d : Gder ⟶ G), IsDerivedSubgroup d →
      ∃ Φ : 𝔅.building F Gder hder ≃ 𝔅.building F G hG,
        ValuationBuildingData.IsEquivariantBuildingIso (𝔅.buildingData F Gder hder)
          (𝔅.buildingData F G hG) (rationalPoints.map d) Φ

/-- The identification of KP Axiom 4.1.1 of the building of the simply connected cover with
`B(G)`: for every actual derived subgroup `d : G_der → G` and simply connected cover
`π : G_sc → G_der`, an isomorphism of buildings `B(G_sc) → B(G)` with
`Φ(h · y) = d(π(h)) · Φ(y)`. -/
def HasSimplyConnectedCoverIdentification : Prop :=
  ∀ (Gder Gsc : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom Gsc.X.hom]
    (hsc : IsConnectedReductive Gsc) (d : Gder ⟶ G) (π : Gsc ⟶ Gder),
    IsSimplyConnectedDerivedCover d π →
      ∃ Φ : 𝔅.building F Gsc hsc ≃ 𝔅.building F G hG,
        ValuationBuildingData.IsEquivariantBuildingIso (𝔅.buildingData F Gsc hsc)
          (𝔅.buildingData F G hG) (rationalPoints.map (π ≫ d)) Φ

/-- KP Axiom 4.1.1 for `G` in the assignment: the clauses for `G` alone
(`ValuationBuildingData.SatisfiesBuildingAxiom`), the comparisons for surjective homomorphisms
with central kernel out of `G`, and the identifications of the buildings of `G_der` and `G_sc`
with `B(G)`. The identification with the building of `G_ad` and the factorization of the action
through `G_ad(F)` follow (`exists_adjointIdentification`, `exists_adjointFactorization`). -/
structure SatisfiesBuildingExistenceAxiom : Prop where
  /-- The building `B(G)` with its action, apartments, tori and stabilizers. -/
  building : (𝔅.buildingData F G hG).SatisfiesBuildingAxiom (𝔅.datum F G hG).realization
  /-- Surjective homomorphisms with central kernel induce equivariant isomorphisms. -/
  centralQuotients : 𝔅.HasCentralQuotientComparisons F G hG
  /-- `B(G_der) = B(G)`. -/
  derivedSubgroups : 𝔅.HasDerivedSubgroupIdentification F G hG
  /-- `B(G_sc) = B(G)`. -/
  simplyConnectedCovers : 𝔅.HasSimplyConnectedCoverIdentification F G hG

variable {𝔅 F G hG}

/-- Under Axiom 4.1.1, an actual adjoint quotient `q : G → G_ad` induces an equivariant
isomorphism `B(G) → B(G_ad)`. -/
theorem SatisfiesBuildingExistenceAxiom.exists_adjointIdentification
    (h : 𝔅.SatisfiesBuildingExistenceAxiom F G hG)
    (Gad : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom Gad.X.hom]
    (had : IsConnectedReductive Gad) {q : G ⟶ Gad} (hq : IsAdjointQuotient q) :
    ∃ Φ : 𝔅.building F G hG ≃ 𝔅.building F Gad had,
      ValuationBuildingData.IsEquivariantBuildingIso (𝔅.buildingData F G hG)
        (𝔅.buildingData F Gad had) (rationalPoints.map q) Φ :=
  h.centralQuotients Gad had q (isCentralSurjection_of_isAdjointQuotient hq)

/-- Under Axiom 4.1.1, the action of `G(F)` on `B(G)` factors through `G_ad(F)`: there is an
action `ρ` of `G_ad(F)` on `B(G)` with `ρ(q(g)) y = g · y`. -/
theorem SatisfiesBuildingExistenceAxiom.exists_adjointFactorization
    (h : 𝔅.SatisfiesBuildingExistenceAxiom F G hG)
    (Gad : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom Gad.X.hom]
    (had : IsConnectedReductive Gad) {q : G ⟶ Gad} (hq : IsAdjointQuotient q) :
    ∃ ρ : rationalPoints Gad →* Equiv.Perm (𝔅.building F G hG),
      ∀ (g : rationalPoints G) (y : 𝔅.building F G hG), ρ (rationalPoints.map q g) y = g • y := by
  obtain ⟨Φ, -, hΦ⟩ := h.exists_adjointIdentification Gad had hq
  refine ⟨{ toFun := fun a => (Φ.trans (MulAction.toPerm a)).trans Φ.symm
            map_one' := ?_
            map_mul' := ?_ }, fun g y => ?_⟩
  · ext y
    simp
  · intro a b
    ext y
    simp [mul_smul]
  · change Φ.symm (rationalPoints.map q g • Φ y) = g • y
    rw [← hΦ, Equiv.symm_apply_apply]

variable (𝔅 F G hG)

/-- KP Axiom 4.1.17 for `G` over `F` in the assignment: for every isomorphism of valued fields
`σ : F → F₂` and every isomorphism `f_G : G ×_{F,σ} F₂ → G₂` of `F₂`-groups, there is an
isomorphism of buildings `f_B : B(G) → B(G₂)` with `f_B(g · y) = f_G(g) · f_B(y)`. -/
def HasIsomorphismCompatibility : Prop :=
  ∀ (F₂ : Type u) [Field F₂] [ValuativeRel F₂] [TopologicalSpace F₂]
    [IsNonarchimedeanLocalField F₂] (σ : F ≃+* F₂), IsValuativeRingEquiv σ →
    ∀ (G₂ : GroupScheme (Spec (CommRingCat.of F₂))) [IsAffineHom G₂.X.hom]
      (hG₂ : IsConnectedReductive G₂)
      (fG : (GroupScheme.baseChange (specMapOfRingEquiv σ)).obj G ≅ G₂),
      ∃ Φ : 𝔅.building F G hG ≃ 𝔅.building F₂ G₂ hG₂,
        ValuationBuildingData.IsEquivariantBuildingIso (𝔅.buildingData F G hG)
          (𝔅.buildingData F₂ G₂ hG₂) (coveringPointsMap σ fG.hom) Φ

/-- KP Definition 4.1.26, as corrected: Bruhat–Tits theory is available for `G` over `F` in the
assignment `𝔅`, i.e. Axioms 4.1.1, 4.1.2, 4.1.4, 4.1.6, 4.1.8, 4.1.9, 4.1.16, 4.1.17, 4.1.20
and 4.1.22 hold. -/
structure IsAvailableFor : Prop where
  /-- Axiom 4.1.1, with the comparisons and identifications. -/
  existenceOfBuilding : 𝔅.SatisfiesBuildingExistenceAxiom F G hG
  /-- Axiom 4.1.2. -/
  boundedSubgroups : (𝔅.buildingData F G hG).HasBoundedOpenStabilizers
  /-- Axiom 4.1.4. -/
  affineStructure :
    (𝔅.buildingData F G hG).SatisfiesAffineApartmentAxiom (𝔅.datum F G hG).splitting
  /-- Axiom 4.1.6. -/
  affineRootSystem : (𝔅.datum F G hG).SatisfiesAffineRootSystemAxiom
  /-- Axiom 4.1.8. -/
  rootGroupAction : (𝔅.datum F G hG).SatisfiesRootGroupActionAxiom
  /-- Axiom 4.1.9 as corrected. -/
  titsSystem : (𝔅.datum F G hG).base.HasTitsSystem
  /-- Axiom 4.1.16. -/
  iwahoriDecomposition : (𝔅.datum F G hG).base.HasIwahoriDecomposition
  /-- Axiom 4.1.17. -/
  isomorphismCompatibility : 𝔅.HasIsomorphismCompatibility F G hG
  /-- Axiom 4.1.20. -/
  bruhatTitsGroupSchemes : (𝔅.datum F G hG).models.SatisfiesModelAxioms (𝔅.datum F G hG).base
  /-- Axiom 4.1.22. -/
  reductiveQuotients :
    (𝔅.datum F G hG).quotients.SatisfiesMorphismAxioms (𝔅.datum F G hG).rootDatum

/-- Bruhat–Tits theory is available in `𝔅` for every connected reductive group over every
nonarchimedean local field in universe `u`. -/
def IsValid : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G), 𝔅.IsAvailableFor F G hG

variable {𝔅 F G hG}

/-- The clauses of Definition 4.1.26 for `G` alone. -/
theorem IsAvailableFor.groupAxioms (h : 𝔅.IsAvailableFor F G hG) :
    (𝔅.datum F G hG).SatisfiesGroupAxioms where
  building := h.existenceOfBuilding.building
  boundedSubgroups := h.boundedSubgroups
  affineStructure := h.affineStructure
  affineRootSystem := h.affineRootSystem
  rootGroupAction := h.rootGroupAction
  titsSystem := h.titsSystem
  iwahoriDecomposition := h.iwahoriDecomposition
  bruhatTitsGroupSchemes := h.bruhatTitsGroupSchemes
  reductiveQuotients := h.reductiveQuotients

/-- Definition 4.1.26 splits into the clauses for `G` alone, the comparisons and
identifications of Axiom 4.1.1, and Axiom 4.1.17. -/
theorem isAvailableFor_iff :
    𝔅.IsAvailableFor F G hG ↔
      (𝔅.datum F G hG).SatisfiesGroupAxioms ∧ 𝔅.HasCentralQuotientComparisons F G hG ∧
        𝔅.HasDerivedSubgroupIdentification F G hG ∧
          𝔅.HasSimplyConnectedCoverIdentification F G hG ∧
            𝔅.HasIsomorphismCompatibility F G hG := by
  constructor
  · intro h
    exact ⟨h.groupAxioms, h.existenceOfBuilding.centralQuotients,
      h.existenceOfBuilding.derivedSubgroups, h.existenceOfBuilding.simplyConnectedCovers,
      h.isomorphismCompatibility⟩
  · rintro ⟨hgrp, hc, hd, hsc, hiso⟩
    exact ⟨⟨hgrp.building, hc, hd, hsc⟩, hgrp.boundedSubgroups, hgrp.affineStructure,
      hgrp.affineRootSystem, hgrp.rootGroupAction, hgrp.titsSystem, hgrp.iwahoriDecomposition,
      hiso, hgrp.bruhatTitsGroupSchemes, hgrp.reductiveQuotients⟩

/-- Projection of Definition 4.1.26 to the Library's partial bundle on the same data. -/
theorem IsAvailableFor.satisfiesPartialBuildingAxioms (h : 𝔅.IsAvailableFor F G hG) :
    (𝔅.datum F G hG).base.SatisfiesPartialBuildingAxioms :=
  h.groupAxioms.satisfiesPartialBuildingAxioms

/-- The partially valid parahoric building data underlying an available datum. -/
def IsAvailableFor.toPartiallyValidParahoricBuildingData (h : 𝔅.IsAvailableFor F G hG) :
    PartiallyValidParahoricBuildingData G :=
  h.groupAxioms.toPartiallyValidParahoricBuildingData

/-- `B(G)` is a building in the sense of KP Definition 1.5.5 (Axiom 4.1.1). -/
theorem IsAvailableFor.isBuilding (h : 𝔅.IsAvailableFor F G hG) :
    AbstractBuilding.IsBuilding (𝔅.datum F G hG).realization.complex
      (𝔅.datum F G hG).realization.apartments :=
  h.existenceOfBuilding.building.isBuilding

/-- The apartments of `B(G)` correspond to the maximal split tori (Axiom 4.1.1). -/
theorem IsAvailableFor.bijOn_torusApartment (h : 𝔅.IsAvailableFor F G hG) :
    Set.BijOn (𝔅.buildingData F G hG).torusApartment (maximalSplitTori G)
      {Y | (𝔅.buildingData F G hG).IsApartment Y} :=
  h.existenceOfBuilding.building.torusApartmentCorrespondence.bijOn

/-- Under Definition 4.1.26 the action of `G(F)` on `B(G)` factors through `G_ad(F)`. -/
theorem IsAvailableFor.exists_adjointFactorization (h : 𝔅.IsAvailableFor F G hG)
    (Gad : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom Gad.X.hom]
    (had : IsConnectedReductive Gad) {q : G ⟶ Gad} (hq : IsAdjointQuotient q) :
    ∃ ρ : rationalPoints Gad →* Equiv.Perm (𝔅.building F G hG),
      ∀ (g : rationalPoints G) (y : 𝔅.building F G hG), ρ (rationalPoints.map q g) y = g • y :=
  h.existenceOfBuilding.exists_adjointFactorization Gad had hq

/-- A valid assignment satisfies Definition 4.1.26 for every group. -/
theorem IsValid.isAvailableFor (h : 𝔅.IsValid) : 𝔅.IsAvailableFor F G hG :=
  h F G hG

end KPBuildingAssignment

end Langlands.Geometry.Building
