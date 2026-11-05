import Langlands.Geometry.Building.AffineIwahoriTits
import Langlands.Geometry.Building.ParahoricBuildingAxioms
import Langlands.Geometry.Building.ChamberIwahori
import Langlands.BruhatTits.IntegralModels.FacetParabolicOrder
import Langlands.Group.TitsSystemRestricted
import Langlands.GroupScheme.Rational.RootProductStatement

/-!
# Axioms 4.1.9 and 4.1.16: the Tits system and the Iwahori decomposition

For building data `P : ParahoricBuildingData G` over a nonarchimedean local field `F`, this
module states KP Axiom 4.1.9 (Tits system) and KP Axiom 4.1.16 (Iwahori decomposition) on the
reduced building `B(G)` of `P`, for the maximal split torus `S` of `P` and every chamber `C` of
its apartment `A = A(S)`.

* `P.zeroStabilizer Y`: `G(F)^0_Y`, the stabilizer of `Y ⊆ B(G)` in `G(F)^0` (KP
  Definition 4.1.3). For a facet this is the parahoric subgroup of KP Definition 4.1.3 and for a
  chamber the Iwahori subgroup. `P.zeroStabilizerIn Y` is the same group as a subgroup of
  `G(F)^0`, and `P.facetZeroStabilizer` is the map `F ↦ G(F)^0_F` on the facets of `B(G)`.
* `P.normalizerInZero`: `N(F) ∩ G(F)^0`, as a subgroup of `G(F)^0`.
* `P.IsBuildingTitsSystem Ca π Sgen`: with `I = G(F)^0_C` for `C` the image of the chamber `Ca`,
  `(I, N(F) ∩ G(F)^0)` is a saturated Tits system in `G(F)^0` with Weyl-group datum `π` and
  finite generating set `Sgen`, and its restricted building (KP Definition 1.5.20) is `B(G)`:
  `F ↦ G(F)^0_F` is a bijection from the facets of `B(G)` onto the admissible parabolic
  subgroups, turning the face relation into reverse inclusion and apartments into apartments.
* `P.HasTitsSystem`: Axiom 4.1.9, for every chamber of `A(S)`.
* `P.IsIwahoriDecompositionAt Ca ν` and `P.HasIwahoriDecomposition`: Axiom 4.1.16, for every
  chamber of `A(S)` and every positive system of roots, given by a generic cocharacter `ν`.

Nothing here asserts that these predicates hold, or that data exist.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Group Langlands.Group.TitsSystem

namespace Langlands.Group.TitsSystem

variable {G : Type*} [Group G] {N : Subgroup G} {W : Type*} [Group W]

/-- `B` lies in every standard parabolic subset `G_X = B W_X B`. -/
theorem subset_standardParabolic (B : Subgroup G) (π : N →* W) (X : Set W) :
    (B : Set G) ⊆ standardParabolic B π X :=
  fun b hb => ⟨1, Subgroup.one_mem _, 1, map_one π, b, hb, 1, B.one_mem, by simp⟩

/-- An admissible parabolic subgroup `g G_X g⁻¹` is parabolic: it contains `g B g⁻¹`. -/
theorem IsAdmissibleParabolic.isParabolic {B : Subgroup G} {π : N →* W} {S : Set W}
    {P : Subgroup G} (hP : IsAdmissibleParabolic B π S P) : IsParabolic B P := by
  obtain ⟨g, X, -, hP⟩ := hP
  refine ⟨g, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  change g * b * g⁻¹ ∈ (P : Set G)
  rw [hP]
  exact ⟨b, subset_standardParabolic B π X hb, rfl⟩

end Langlands.Group.TitsSystem

namespace Langlands.Geometry.Building.ParahoricBuildingData

open BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-! ### Stabilizers in `G(F)^0` (KP Definition 4.1.3) -/

/-- `G(F)^0_Y`: the stabilizer of `Y ⊆ B(G)` in `G(F)^0` (KP Definition 4.1.3). For a facet `Y`
it is the parahoric subgroup attached to `Y`, and for a chamber the Iwahori subgroup. It is
distinct from the pointwise fixer `P.zeroFixer` and from the Chapter 7 group `P.parahoric`. -/
def zeroStabilizer (Y : Set P.ReducedBuilding) : Subgroup (rationalPoints G) :=
  P.zeroSubgroup ⊓ MulAction.stabilizer (rationalPoints G) Y

theorem mem_zeroStabilizer {Y : Set P.ReducedBuilding} {g : rationalPoints G} :
    g ∈ P.zeroStabilizer Y ↔ g ∈ P.zeroSubgroup ∧ g • Y = Y :=
  Iff.rfl

/-- `G(F)^0_Y` as a subgroup of the group `G(F)^0`. -/
def zeroStabilizerIn (Y : Set P.ReducedBuilding) : Subgroup P.zeroSubgroup :=
  (MulAction.stabilizer (rationalPoints G) Y).subgroupOf P.zeroSubgroup

theorem map_zeroStabilizerIn (Y : Set P.ReducedBuilding) :
    (P.zeroStabilizerIn Y).map P.zeroSubgroup.subtype = P.zeroStabilizer Y := by
  rw [zeroStabilizerIn, Subgroup.subgroupOf_map_subtype, zeroStabilizer, inf_comm]

theorem mem_zeroStabilizerIn {Y : Set P.ReducedBuilding} {g : P.zeroSubgroup} :
    g ∈ P.zeroStabilizerIn Y ↔ (g : rationalPoints G) • Y = Y :=
  Subgroup.mem_subgroupOf

/-- The stabilizer `G(F)^0_F` of a facet `F` of `B(G)`, as a subgroup of `G(F)^0`. -/
def facetZeroStabilizer (Fc : BuildingFacet P.toValuationBuildingData) :
    Subgroup P.zeroSubgroup :=
  P.zeroStabilizerIn Fc.val

/-- The Iwahori subgroup `I = G(F)^0_C` of KP Axiom 4.1.9, for `C` the image in `B(G)` of a
chamber `Ca` of `A(S)`, as a subgroup of `G(F)^0`. -/
def chamberZeroStabilizerIn (Ca : Set P.Apartment) : Subgroup P.zeroSubgroup :=
  P.zeroStabilizerIn (P.apartmentMap '' Ca)

/-- For each apartment `h · A(S)` of `B(G)`, the set of stabilizers `G(F)^0_F` of the facets `F`
of `B(G)` contained in it. -/
def apartmentFacetStabilizers : Set (Set (Subgroup P.zeroSubgroup)) :=
  {Q | ∃ h : rationalPoints G,
    Q = P.facetZeroStabilizer '' {Fc | Fc.val ⊆ h • P.apartmentImage}}

/-! ### Axiom 4.1.9 -/

/-- KP Axiom 4.1.9 at the chamber `C = Ca` of `A(S)`, for a Weyl-group datum
`π : N(F) ∩ G(F)^0 →* W` and a set `Sgen ⊆ W`. With `I = G(F)^0_C`:

* `(I, N(F) ∩ G(F)^0, Sgen)` is a Tits system in `G(F)^0` (KP Definition 1.4.1, TS 1–TS 4)
  with `Sgen` finite, and it is saturated (TS 5);
* its restricted building (KP Definition 1.5.20, in the parabolic description of KP
  Remark 1.5.7) is `B(G)`: `F ↦ G(F)^0_F` is a bijection from the facets of `B(G)` onto the
  admissible parabolic subgroups, the face relation `F ≺ F'` becomes `G(F)^0_{F'} ⊆ G(F)^0_F`,
  and the apartments `h · A(S)` of `B(G)` correspond to the apartments of the restricted
  building. -/
structure IsBuildingTitsSystem (Ca : Set P.Apartment) {W : Type u} [Group W]
    (π : P.normalizerInZero →* W) (Sgen : Set W) : Prop where
  /-- TS 1–TS 4: `(I, N(F) ∩ G(F)^0)` is a Tits system in `G(F)^0` with Weyl group `W`. -/
  isTitsSystem : IsTitsSystem (P.chamberZeroStabilizerIn Ca) P.normalizerInZero π Sgen
  /-- `Sgen` is finite, as required for the restricted building (KP Proposition 1.5.18). -/
  finite : Sgen.Finite
  /-- TS 5: the Tits system is saturated. -/
  isSaturated : IsSaturated (P.chamberZeroStabilizerIn Ca) P.normalizerInZero
  /-- The stabilizers of the facets of `B(G)` are exactly the admissible parabolic subgroups,
  each facet giving a different one. -/
  bijOn_facetZeroStabilizer : Set.BijOn P.facetZeroStabilizer Set.univ
    {Q | IsAdmissibleParabolic (P.chamberZeroStabilizerIn Ca) π Sgen Q}
  /-- The face relation of `B(G)` is the opposite of inclusion of stabilizers. -/
  facetPrecedes_iff : ∀ Fc Fc' : BuildingFacet P.toValuationBuildingData,
    FacetPrecedes P.toValuationBuildingData Fc Fc' ↔
      P.facetZeroStabilizer Fc' ≤ P.facetZeroStabilizer Fc
  /-- The apartments of `B(G)` are the apartments of the restricted building. -/
  apartmentFacetStabilizers_eq : P.apartmentFacetStabilizers =
    restrictedApartments (P.chamberZeroStabilizerIn Ca) π Sgen

/-- KP Axiom 4.1.9 for the apartment `A(S)`: for every chamber `C` of `A(S)` there are a Weyl
group `W`, a datum `π : N(F) ∩ G(F)^0 →* W` and a finite `Sgen ⊆ W` making
`(G(F)^0_C, N(F) ∩ G(F)^0)` a saturated Tits system in `G(F)^0` whose restricted building is
`B(G)`. -/
def HasTitsSystem : Prop :=
  ∀ Ca : Set P.Apartment, AffineRootSystem.IsChamber P.affineRoots Ca →
    ∃ (W : Type u) (_ : Group W) (π : P.normalizerInZero →* W) (Sgen : Set W),
      P.IsBuildingTitsSystem Ca π Sgen

variable {P}

/-- Under Axiom 4.1.9, the stabilizer `G(F)^0_F` of every facet is a parabolic subgroup of the
Tits system. -/
theorem IsBuildingTitsSystem.isParabolic_facetZeroStabilizer {Ca : Set P.Apartment}
    {W : Type u} [Group W] {π : P.normalizerInZero →* W} {Sgen : Set W}
    (h : P.IsBuildingTitsSystem Ca π Sgen) (Fc : BuildingFacet P.toValuationBuildingData) :
    IsParabolic (P.chamberZeroStabilizerIn Ca) (P.facetZeroStabilizer Fc) :=
  IsAdmissibleParabolic.isParabolic (h.bijOn_facetZeroStabilizer.mapsTo (Set.mem_univ Fc))

/-- Under Axiom 4.1.9, every admissible parabolic subgroup is the stabilizer of a facet. -/
theorem IsBuildingTitsSystem.exists_facetZeroStabilizer_eq {Ca : Set P.Apartment}
    {W : Type u} [Group W] {π : P.normalizerInZero →* W} {Sgen : Set W}
    (h : P.IsBuildingTitsSystem Ca π Sgen) {Q : Subgroup P.zeroSubgroup}
    (hQ : IsAdmissibleParabolic (P.chamberZeroStabilizerIn Ca) π Sgen Q) :
    ∃ Fc : BuildingFacet P.toValuationBuildingData, P.facetZeroStabilizer Fc = Q := by
  obtain ⟨Fc, -, hFc⟩ := h.bijOn_facetZeroStabilizer.surjOn hQ
  exact ⟨Fc, hFc⟩

variable (P)

/-! ### Axiom 4.1.16 -/

/-- `U(ν)(F) ∩ G(F)^0_Y`, for the actual Dynamic unipotent radical `U(ν)` of the cocharacter
`ν` of `S`. For generic `ν`, `U(ν)` is the unipotent radical of the minimal parabolic subgroup
containing `S` attached to the positive system `{a | ⟨a, ν⟩ > 0}`. -/
def zeroStabilizerUnipotentPoints (ν : cocharacterLattice P.S) (Y : Set P.ReducedBuilding) :
    Subgroup (rationalPoints G) :=
  (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ P.i)).carrier (Over.mk (𝟙 _)) ⊓
    P.zeroStabilizer Y

/-- The product map `(U(ν)(F) ∩ G(F)^0_Y) × Z(F)^0 × (U(-ν)(F) ∩ G(F)^0_Y) → G(F)`,
`(u, z, v) ↦ u z v`, with `Z(F)^0` mapped by the centralizer inclusion `j : Z → G`. -/
def zeroStabilizerProduct (Y : Set P.ReducedBuilding) (ν : cocharacterLattice P.S)
    (p : P.zeroStabilizerUnipotentPoints ν Y × P.centralizerZero ×
      P.zeroStabilizerUnipotentPoints (-ν) Y) : rationalPoints G :=
  (p.1 : rationalPoints G) *
    rationalPoints.map P.centralizer.j (p.2.1 : rationalPoints P.centralizer.Z) *
      (p.2.2 : rationalPoints G)

/-- `ψ` is the smallest affine functional on `A(S)` with derivative `α` that is non-negative on
`Ω`, for the pointwise order (the functional `ψ_a` of KP Axiom 4.1.16). -/
def IsLeastNonnegativeFunctional (α : relativeRoots P.i) (Ω : Set P.Apartment)
    (ψ : P.Apartment →ᵃ[ℝ] ℝ) : Prop :=
  ψ.linear = rootForm P.i α ∧ (∀ x ∈ Ω, 0 ≤ ψ x) ∧
    ∀ ψ' : P.Apartment →ᵃ[ℝ] ℝ, ψ'.linear = rootForm P.i α → (∀ x ∈ Ω, 0 ≤ ψ' x) →
      ∀ x, ψ x ≤ ψ' x

/-- The ordered product `∏_j U_{ψ(a_j)} → G(F)`, `(u_j) ↦ u_0 u_1 ⋯ u_{n-1}`, for roots
`a_0, …, a_{n-1}` and affine functionals `ψ(a_j)`. -/
def orderedAffineRootProduct {n : ℕ} (a : Fin n → relativeRoots P.i)
    (ψ : relativeRoots P.i → (P.Apartment →ᵃ[ℝ] ℝ))
    (u : ∀ j, P.affineRootGroup (a j) (ψ (a j))) : rationalPoints G :=
  (List.ofFn fun j => (u j : rationalPoints G)).prod

/-- The second sentence of KP Axiom 4.1.16 for the positive system of `ν`: for the smallest
functionals `ψ_a` of the non-divisible roots `a`, the product map
`∏_{a ∈ Φ^+_{nd}} U_{ψ_a} → U(ν)(F) ∩ I` is a bijection for every order of the factors. An order
is an injective enumeration `a_0, …, a_{n-1}` of the non-divisible roots `a` with
`⟨a, ν⟩ > 0`. -/
def IsOrderedRootProductBijective (Ca : Set P.Apartment) (ν : cocharacterLattice P.S) :
    Prop :=
  ∀ ψ : relativeRoots P.i → (P.Apartment →ᵃ[ℝ] ℝ),
    (∀ α : relativeRoots P.i, (α : characterLattice P.S) ∈ RelativeRoot.indivisibleRoots P.i →
      P.IsLeastNonnegativeFunctional α Ca (ψ α)) →
    ∀ (n : ℕ) (a : Fin n → relativeRoots P.i), Function.Injective a →
      Set.range (fun j => (a j : characterLattice P.S)) =
        RelativeRoot.indivisiblePositiveRoots P.i ν →
      Function.Injective (P.orderedAffineRootProduct a ψ) ∧
        Set.range (P.orderedAffineRootProduct a ψ) =
          (P.zeroStabilizerUnipotentPoints ν (P.apartmentMap '' Ca) : Set (rationalPoints G))

/-- KP Axiom 4.1.16 at the chamber `C = Ca` of `A(S)` and the positive system `Φ^+` of the
generic cocharacter `ν`, with `I = G(F)^0_C`, `U^+ = U(ν)` and `U^- = U(-ν)`. -/
structure IsIwahoriDecompositionAt (Ca : Set P.Apartment) (ν : cocharacterLattice P.S) :
    Prop where
  /-- The product map `(U^+(F) ∩ I) × Z(F)^0 × (U^-(F) ∩ I) → I` is injective. -/
  injective_product : Function.Injective (P.zeroStabilizerProduct (P.apartmentMap '' Ca) ν)
  /-- The product map `(U^+(F) ∩ I) × Z(F)^0 × (U^-(F) ∩ I) → G(F)` has image `I`. -/
  range_product : Set.range (P.zeroStabilizerProduct (P.apartmentMap '' Ca) ν) =
    (P.zeroStabilizer (P.apartmentMap '' Ca) : Set (rationalPoints G))
  /-- For every non-divisible root `a` the smallest functional `ψ_a` exists. -/
  exists_isLeastNonnegativeFunctional : ∀ α : relativeRoots P.i,
    (α : characterLattice P.S) ∈ RelativeRoot.indivisibleRoots P.i →
      ∃ ψ, P.IsLeastNonnegativeFunctional α Ca ψ
  /-- `∏_{a ∈ Φ^+_{nd}} U_{ψ_a} → U^+(F) ∩ I` is bijective in every order. -/
  orderedProduct_pos : P.IsOrderedRootProductBijective Ca ν
  /-- `∏_{a ∈ Φ^-_{nd}} U_{ψ_a} → U^-(F) ∩ I` is bijective in every order. -/
  orderedProduct_neg : P.IsOrderedRootProductBijective Ca (-ν)

/-- KP Axiom 4.1.16 for the apartment `A(S)`: the Iwahori decomposition holds for every chamber
of `A(S)` and every positive system of roots. A positive system is `{a | ⟨a, ν⟩ > 0}` for a
generic cocharacter `ν` of `S` (`IsGenericCocharacter`). -/
def HasIwahoriDecomposition : Prop :=
  ∀ Ca : Set P.Apartment, AffineRootSystem.IsChamber P.affineRoots Ca →
    ∀ ν : cocharacterLattice P.S, IsGenericCocharacter P.i ν → P.IsIwahoriDecompositionAt Ca ν

variable {P}

/-- Under Axiom 4.1.16, `Z(F)^0` lies in the Iwahori subgroup `I = G(F)^0_C`. -/
theorem IsIwahoriDecompositionAt.map_centralizerZero_le {Ca : Set P.Apartment}
    {ν : cocharacterLattice P.S} (h : P.IsIwahoriDecompositionAt Ca ν) :
    P.centralizerZero.map (rationalPoints.map P.centralizer.j) ≤
      P.zeroStabilizer (P.apartmentMap '' Ca) := by
  rintro _ ⟨z, hz, rfl⟩
  have hmem : P.zeroStabilizerProduct (P.apartmentMap '' Ca) ν (1, ⟨z, hz⟩, 1) ∈
      Set.range (P.zeroStabilizerProduct (P.apartmentMap '' Ca) ν) := ⟨_, rfl⟩
  rw [h.range_product] at hmem
  simpa [zeroStabilizerProduct] using hmem

/-- The functional `ψ_a` of KP Axiom 4.1.16 is unique. -/
theorem IsLeastNonnegativeFunctional.unique {α : relativeRoots P.i} {Ω : Set P.Apartment}
    {ψ ψ' : P.Apartment →ᵃ[ℝ] ℝ} (h : P.IsLeastNonnegativeFunctional α Ω ψ)
    (h' : P.IsLeastNonnegativeFunctional α Ω ψ') : ψ = ψ' :=
  AffineMap.ext fun x =>
    le_antisymm (h.2.2 ψ' h'.1 h'.2.1 x) (h'.2.2 ψ h.1 h.2.1 x)

/-- `U_{ψ_a} ⊆ U_{a,C,0}`: the factor `U_{ψ_a}` fixes `C`, by the Library's
`affineRootGroup_le_rootFixer`. -/
theorem IsLeastNonnegativeFunctional.affineRootGroup_le_rootFixer {α : relativeRoots P.i}
    {Ω : Set P.Apartment} {ψ : P.Apartment →ᵃ[ℝ] ℝ}
    (h : P.IsLeastNonnegativeFunctional α Ω ψ) :
    P.affineRootGroup α ψ ≤ P.rootFixer α Ω :=
  P.affineRootGroup_le_rootFixer h.1 h.2.1

end Langlands.Geometry.Building.ParahoricBuildingData
