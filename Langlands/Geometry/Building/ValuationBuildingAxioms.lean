import Langlands.Geometry.Building.ValuationBuildingData
import Langlands.Geometry.Building.KPApartmentAxioms

/-!
# Kaletha–Prasad axioms on building data

For building data `B : ValuationBuildingData G` over a nonarchimedean local field `F`, this
module states on `B` the clauses of the corrected KP Definition 4.1.26 that can be stated with
the objects of `B` alone, and proves those that hold by construction.

* `B.SatisfiesApartmentAxioms`: V 6, V 7 and AS 2–AS 5 for the class `A(S)` of `B`, the
  published `KPApartmentData.SatisfiesApartmentAxioms` for the centralizer of `B`.
* `B.HasBoundedOpenStabilizers`: KP Axiom 4.1.2 for the reduced building of `B`.
* KP Axiom 4.1.4 (A 1), proved: the action map `f = B.normalizerAction : N(F) → Aff(A)`, its
  derivative, and the translations by `Z(F)`.
* KP Axiom 4.1.8 (1), proved: `U_ψ` fixes the half-apartment `A_{ψ ≥ 0}` pointwise.
* The apartments `g · A(S)` of the building, and the clause of KP Axiom 4.1.1 that the
  stabilizer of `A(S)` in `G(F)` is `N(F)` (`B.HasNormalizerApartmentStabilizer`).
* AS 6 of KP Axiom 4.1.6 (`B.HasCompatibleApartmentFacets`).

The remaining clauses of the corrected Definition 4.1.26 are not stated here. They need
objects that are not available (`m(u)`, `G(F)^0`, `Z(F)^0`, integral models), or they concern
the construction `G ↦ B(G)` rather than one `G`. Nothing here asserts that any of these
predicates holds for given data, or that data exist.
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

/-! ### The axioms on the apartment class (V 6, V 7, AS 2–AS 5) and Axiom 4.1.2 -/

/-- KP axiom V 7 (Definition 6.1.2) for every valuation of the class `A(S)` of `B`. -/
abbrev IsTopologyCompatible : Prop :=
  B.apartment.IsTopologyCompatible

/-- V 6 on `Z(F)`, V 7 and AS 2–AS 5 (KP Definition 6.1.2 and Axiom 4.1.6) for the class
`A(S)` of `B` and the actual centralizer of `B`. Only part of the corrected KP
Definition 4.1.26. -/
abbrev SatisfiesApartmentAxioms : Prop :=
  B.apartment.SatisfiesApartmentAxioms B.centralizer

/-- V 6 is part of the data `B`, so `B.SatisfiesApartmentAxioms` asks for V 7 and AS 2–AS 5
only. -/
theorem satisfiesApartmentAxioms_iff :
    B.SatisfiesApartmentAxioms ↔
      B.IsTopologyCompatible ∧
        AffineRootSystem.IsAffineRootSystemWithRankZero B.apartment.extendedAffineRoots ∧
        AffineRootSystem.derivativeRoots B.apartment.extendedAffineRoots =
          Set.range (rootForm B.i) ∧
        AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots ∧
        AffineRootSystem.derivativeRoots B.affineRoots = Set.range (rootForm B.i) ∧
        (∀ ψ ∈ B.apartment.extendedAffineRoots, ψ ∈ B.affineRoots ∨ (2 : ℝ) • ψ ∈ B.affineRoots) ∧
        AffineRootSystem.affineWeylGroup B.affineRoots ≤ B.apartment.normalizerAffineEquiv.range ∧
        B.apartment.normalizerAffineEquiv.range ≤
          AffineRootSystem.extendedAffineWeylGroup B.affineRoots ∧
        (IsSimplyConnected G →
          B.apartment.normalizerAffineEquiv.range =
            AffineRootSystem.affineWeylGroup B.affineRoots) ∧
        (IsQuasiSplit G → IsAdjoint G →
          B.apartment.normalizerAffineEquiv.range =
            AffineRootSystem.extendedAffineWeylGroup B.affineRoots) := by
  constructor
  · intro h
    exact ⟨h.topologyCompatible, h.isAffineRootSystem_extendedAffineRoots,
      h.derivativeRoots_extendedAffineRoots, h.isAffineRootSystem_affineRoots,
      h.derivativeRoots_affineRoots, h.mem_or_two_smul_mem, h.affineWeylGroup_le_range,
      h.range_le_extendedAffineWeylGroup, h.range_eq_affineWeylGroup_of_isSimplyConnected,
      h.range_eq_extendedAffineWeylGroup_of_isQuasiSplit_of_isAdjoint⟩
  · rintro ⟨h7, h2, h2', h3, h3', h4, h5, h5', h5sc, h5ad⟩
    exact ⟨B.isOmegaCompatible, h7, h2, h2', h3, h3', h4, h5, h5', h5sc, h5ad⟩

/-- KP Axiom 4.1.2 for the reduced building of `B`: every `K_y = G(F)^1_y` is a bounded open
subgroup of `G(F)`. -/
abbrev HasBoundedOpenStabilizers : Prop :=
  B.apartment.HasBoundedOpenStabilizers

/-! ### Axiom 4.1.4 (A 1): the action of `N(F)` on the apartment -/

/-- The action map `f : N(F) → Aff(A)` of KP Axiom 4.1.4 (A 1). -/
abbrev normalizerAction : normalizerPoints B.i →* (B.Apartment ≃ᵃ[ℝ] B.Apartment) :=
  B.apartment.normalizerAffineEquiv

theorem normalizerAction_apply (n : normalizerPoints B.i) (x : B.Apartment) :
    B.normalizerAction n x = n • x :=
  rfl

/-- The derivative of `f(n)` is the action of `n` on `TranslationSpace B.i` (`V(S)` modulo the
common kernel of the roots) induced by its action on `V(S)` (KP Axiom 4.1.4 (A 1)). -/
theorem normalizerAction_linear (n : normalizerPoints B.i) :
    (B.normalizerAction n).linear = translationAction B.i n :=
  rfl

/-- `z ∈ Z(F)` acts on `A` as the translation by the class of `ν(z) = -ω_Z(z)` (KP
Axiom 4.1.4 (A 1)). -/
theorem normalizerAction_centralizer (z : rationalPoints B.centralizer.Z) :
    B.normalizerAction (B.centralizer.toNormalizer z) =
      AffineEquiv.constVAdd ℝ B.Apartment
        (Submodule.Quotient.mk (B.translation z).toAdd : TranslationSpace B.i) :=
  B.isOmegaCompatible.normalizerAffineEquiv_eq z

/-- `Z(F)^1`, the kernel of `ν`, acts trivially on `A`. -/
theorem normalizerAction_centralizer_eq_one {z : rationalPoints B.centralizer.Z}
    (hz : z ∈ rationalCommonNormKernel B.centralizer.Z) :
    B.normalizerAction (B.centralizer.toNormalizer z) = 1 :=
  AffineEquiv.ext fun x => B.isOmegaCompatible.smul_eq_self hz x

/-! ### Axiom 4.1.8 (1): `U_ψ` fixes the half-apartment `A_{ψ ≥ 0}` -/

/-- For an affine functional `ψ` with derivative a root `a`, the group `U_ψ` fixes the image of
the half-apartment `A_{ψ ≥ 0} = {x | ψ(x) ≥ 0}` pointwise (KP Axiom 4.1.8 (1) and Fact 7.6.7,
there for `ψ ∈ Ψ`). -/
theorem affineRootGroup_le_pointwiseFixer {α : relativeRoots B.i} {ψ : B.Apartment →ᵃ[ℝ] ℝ}
    (hψ : ψ.linear = rootForm B.i α) :
    B.affineRootGroup α ψ ≤ B.pointwiseFixer (B.apartmentMap '' {x | 0 ≤ ψ x}) := by
  intro u hu
  rw [B.apartment.mem_pointwiseFixer]
  rintro _ ⟨x, hx, rfl⟩
  have h0 : u ∈ B.apartment.filtration x α 0 := by
    change u ∈ B.apartment.affineRootGroup α ψ at hu
    rw [B.apartment.affineRootGroup_eq_filtration hψ x] at hu
    exact B.apartment.filtration_antitone x α hx hu
  have hsharp : u ∈ B.sharpFixer {x} := by
    refine B.apartment.rootFixer_le_sharpFixer α {x} ?_
    rw [B.apartment.rootFixer_singleton]
    exact h0
  exact B.mem_fixer.1 (B.sharpFixer_le_fixer x hsharp)

/-! ### Apartments and Axiom 4.1.1 -/

/-- The apartment `A(S)` of the building: the image of `A(S)` in `B(G)`. -/
def apartmentImage : Set B.ReducedBuilding :=
  Set.range B.apartmentMap

/-- An apartment of `B(G)`: a `G(F)`-translate `g · A(S)` of the apartment of `S` (KP
Axiom 4.1.1, Proposition 7.6.3 (1) and Corollary 7.6.9; `g · A(S)` is the apartment of the
maximal split torus `g S g⁻¹`). -/
def IsApartment (Y : Set B.ReducedBuilding) : Prop :=
  ∃ g : rationalPoints G, Y = g • B.apartmentImage

theorem isApartment_apartmentImage : B.IsApartment B.apartmentImage :=
  ⟨1, (one_smul _ _).symm⟩

theorem IsApartment.smul {Y : Set B.ReducedBuilding} (hY : B.IsApartment Y)
    (g : rationalPoints G) : B.IsApartment (g • Y) := by
  obtain ⟨h, rfl⟩ := hY
  exact ⟨g * h, (mul_smul g h _).symm⟩

/-- Every point of the building lies in an apartment. -/
theorem exists_isApartment_mem (y : B.ReducedBuilding) :
    ∃ Y, B.IsApartment Y ∧ y ∈ Y := by
  obtain ⟨g, x, rfl⟩ := B.exists_smul_apartmentMap y
  exact ⟨g • B.apartmentImage, ⟨g, rfl⟩, Set.smul_mem_smul_set ⟨x, rfl⟩⟩

/-- `N(F)` stabilizes the apartment of `S`. -/
theorem normalizerPoints_le_stabilizer_apartmentImage :
    normalizerPoints B.i ≤ MulAction.stabilizer (rationalPoints G) B.apartmentImage := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff]
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨(⟨g, hg⟩ : normalizerPoints B.i) • x,
      (B.normalizer_smul_apartmentMap ⟨g, hg⟩ x).symm⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨B.apartmentMap ((⟨g, hg⟩ : normalizerPoints B.i)⁻¹ • x), ⟨_, rfl⟩, ?_⟩
    change ((⟨g, hg⟩ : normalizerPoints B.i) : rationalPoints G) • _ = _
    rw [B.normalizer_smul_apartmentMap, smul_inv_smul]

/-- The clause of KP Axiom 4.1.1 that the stabilizer in `G(F)` of the apartment `A(S)` is
`N(F)` (KP Proposition 7.6.8). `N(F)` stabilizes `A(S)` by construction
(`normalizerPoints_le_stabilizer_apartmentImage`), so the clause asks for the converse. -/
def HasNormalizerApartmentStabilizer : Prop :=
  MulAction.stabilizer (rationalPoints G) B.apartmentImage = normalizerPoints B.i

theorem hasNormalizerApartmentStabilizer_iff :
    B.HasNormalizerApartmentStabilizer ↔
      ∀ g : rationalPoints G, g • B.apartmentImage = B.apartmentImage →
        g ∈ normalizerPoints B.i := by
  constructor
  · intro h g hg
    rw [← h]
    exact hg
  · intro h
    exact le_antisymm (fun g hg => h g hg) B.normalizerPoints_le_stabilizer_apartmentImage

/-- Under the clause of Axiom 4.1.1, `g · A(S) = A(S)` if and only if `g ∈ N(F)`. -/
theorem HasNormalizerApartmentStabilizer.smul_apartmentImage_eq_iff
    (h : B.HasNormalizerApartmentStabilizer) (g : rationalPoints G) :
    g • B.apartmentImage = B.apartmentImage ↔ g ∈ normalizerPoints B.i := by
  rw [← h]
  exact MulAction.mem_stabilizer_iff.symm

/-! ### AS 6 -/

/-- AS 6 of KP Axiom 4.1.6 for the apartment `A(S)` of `B`: the map `A(S) → B(G)` is injective,
and the facets of the building that meet its image are exactly the images of the facets of
`A(S)` for the affine roots `Ψ`. -/
structure HasCompatibleApartmentFacets : Prop where
  /-- `A(S)` embeds into the building. -/
  injective : Function.Injective B.apartmentMap
  /-- A facet of `B(G)` meeting `A(S)` is the image of a facet of `A(S)`. -/
  exists_isFacet_of_isFacet : ∀ Y : Set B.ReducedBuilding, B.IsFacet Y →
    (Y ∩ B.apartmentImage).Nonempty →
      ∃ Fa : Set B.Apartment, AffineRootSystem.IsFacet B.affineRoots Fa ∧ Y = B.apartmentMap '' Fa

/-- Facets of the building are nonempty. -/
theorem IsFacet.nonempty {Y : Set B.ReducedBuilding} (hY : B.IsFacet Y) : Y.Nonempty := by
  obtain ⟨g, _, ⟨x, rfl⟩, rfl⟩ := hY
  exact ⟨_, x, AffineRootSystem.mem_facet_self _ x, rfl⟩

/-- Under AS 6, a subset of `A(S)` is a facet of the apartment exactly when its image is a facet
of the building. -/
theorem HasCompatibleApartmentFacets.isFacet_image_iff (h : B.HasCompatibleApartmentFacets)
    {Fa : Set B.Apartment} :
    B.IsFacet (B.apartmentMap '' Fa) ↔ AffineRootSystem.IsFacet B.affineRoots Fa := by
  refine ⟨fun hY => ?_, B.isFacet_image⟩
  obtain ⟨_, x, hx, rfl⟩ := hY.nonempty
  obtain ⟨Fa', hF', heq⟩ := h.exists_isFacet_of_isFacet _ hY
    ⟨B.apartmentMap x, ⟨x, hx, rfl⟩, ⟨x, rfl⟩⟩
  rwa [h.injective.image_injective heq]

end Langlands.Geometry.Building.ValuationBuildingData
