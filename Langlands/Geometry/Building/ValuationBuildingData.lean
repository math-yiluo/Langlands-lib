import Langlands.Geometry.Building.KPCentralizerCompatibility
import Langlands.Geometry.Building.KPRootFixerPlus
import Langlands.GroupScheme.Rational.SplitTorus

/-!
# Building data for an `ω`-compatible valuation of the root datum

Let `F` be a nonarchimedean local field and `G` a connected reductive group over `F`.
`ValuationBuildingData G` bundles the data from which KP Chapter 7 builds `B(G)` ("The
Bruhat–Tits Building for a Valuation of the Root Datum"), for one maximal split torus:

* a maximal split torus `i : S → G` (the published `IsMaximalSplitTorus`);
* an `N(F)`-stable equipollence class `A(S)` of valuations of the root datum of `(G, S)`
  (KP Definitions 6.1.2 and 6.1.7, with the `N(F)`-action of KP 6.1.8), as
  `KPApartmentData i (localFieldOrder F)`;
* the actual centralizer `Z = Z_G(S)` (`CentralizerDatum i`), and the axiom V 6 of
  KP Definition 6.1.2 for `A(S)` on all of `Z(F)` (`ω`-compatibility).

Under stable names in the namespace `ValuationBuildingData`, the module exposes the
apartment and the reduced building `B(G)` of KP (7.6.2) with its `G(F)`-action. It also
exposes the actual root groups `U_a(F)` and their filtrations, the affine roots, and the
facets, chambers, vertices and special points of the apartment and of the building. Last
come the full and pointwise fixers and `K_y = G(F)^1 ∩ G(F)_y`. The actions of `N(F)` and
`Z(F)` on the apartment are recorded.

`ValuationBuildingData G` is a type of data. Nothing here asserts that it is inhabited.
The existence of such data for every connected reductive `G` (KP Chapters 7 and 9, and the
comparison `Cartan.CentralizerValuationComparisonStatement`) is not assumed. The axiom V 7
of KP Definition 6.1.2 (compatibility with the topology) is not part of these data. Nor is
AS 5 of KP Axiom 4.1.6, which the corrected opening of KP Chapter 7 also assumes.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A maximal split torus is a closed immersion, hence a monomorphism of schemes. -/
theorem mono_of_isMaximalSplitTorus {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) : Mono i.hom.hom.left :=
  haveI : IsClosedImmersion i.hom.hom.left := hi.isSplitSubtorus.2
  inferInstance

variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]

/-- Building data for an `ω`-compatible valuation of the root datum of `G` over the
nonarchimedean local field `F`. The fields are a maximal split torus `i : S → G` of the
connected reductive group `G`, an `N(F)`-stable equipollence class of valuations of the root
datum of `(G, S)` normalized by `ω = ord_F` (KP Definitions 6.1.2, 6.1.7 and 6.1.8; KP
Chapter 7, opening paragraphs), the actual centralizer `Z_G(S)`, and the axiom V 6 of KP
Definition 6.1.2 on all of `Z(F)`. -/
structure ValuationBuildingData : Type (u + 1) where
  /-- `G` is a connected reductive group. -/
  isConnectedReductive : IsConnectedReductive G
  /-- The maximal split torus `S`. -/
  S : CommGroupScheme (Spec (CommRingCat.of F))
  /-- The inclusion `S → G`. -/
  i : S.toGrp ⟶ G
  isMaximalSplitTorus : IsMaximalSplitTorus i
  /-- The equipollence class `A(S)` of valuations of the root datum of `(G, S)`. -/
  apartment : haveI := mono_of_isMaximalSplitTorus isMaximalSplitTorus
    KPApartmentData i (localFieldOrder F)
  /-- The actual centralizer `Z = Z_G(S)`. -/
  centralizer : CentralizerDatum i
  /-- Axiom V 6 of KP Definition 6.1.2 for every valuation of `A(S)` and all of `Z(F)`. -/
  isOmegaCompatible : haveI := mono_of_isMaximalSplitTorus isMaximalSplitTorus
    apartment.IsOmegaCompatible centralizer

namespace ValuationBuildingData

variable {G} (B : ValuationBuildingData G)

instance : Mono B.i.hom.hom.left :=
  mono_of_isMaximalSplitTorus B.isMaximalSplitTorus

/-! ### The apartment and the reduced building -/

/-- The apartment `A(S)`: the points of the equipollence class, an affine space over
`TranslationSpace B.i = V(S)/V(S)^Φ`. -/
abbrev Apartment : Type u :=
  B.apartment.Apartment

/-- The reduced building `B(G)` of KP Remark 7.6.5, the quotient (7.6.2) of `G(F) × A(S)`. -/
abbrev ReducedBuilding : Type u :=
  B.apartment.ReducedBuilding

/-- The map `A(S) → B(G)`, `x ↦ [(1, x)]`. -/
abbrev apartmentMap (x : B.Apartment) : B.ReducedBuilding :=
  B.apartment.apartmentMap x

/-- The building is the union of the `G(F)`-translates of the apartment. -/
theorem exists_smul_apartmentMap (y : B.ReducedBuilding) :
    ∃ (g : rationalPoints G) (x : B.Apartment), g • B.apartmentMap x = y :=
  B.apartment.exists_smul_apartmentMap y

/-- `N(F) ⊆ G(F)` acts on the image of the apartment through its action on `A(S)`
(KP 6.1.8). -/
theorem normalizer_smul_apartmentMap (n : normalizerPoints B.i) (x : B.Apartment) :
    (n : rationalPoints G) • B.apartmentMap x = B.apartmentMap (n • x) :=
  (B.apartment.apartmentMap_smul n x).symm

/-! ### Actual root groups and their filtrations -/

/-- The actual root group `U_a(F)`: the `F`-points of the relative root subgroup functor of `a`
for `S`. -/
abbrev rootGroup (a : characterLattice B.S) : Subgroup (rationalPoints G) :=
  rootGroupPoints B.i a

theorem rootGroup_eq (a : characterLattice B.S) :
    B.rootGroup a = (RelativeRoot.subgroup B.i a).carrier (Over.mk (𝟙 _)) :=
  rfl

/-- The filtration `U_{a,x,r} = {u ∈ U_a(F) | x_a(u) ≥ r}` (KP Definition 6.1.2). -/
abbrev filtration (x : B.Apartment) (a : characterLattice B.S) (r : ℝ) :
    Subgroup (rationalPoints G) :=
  B.apartment.filtration x a r

theorem filtration_le_rootGroup (x : B.Apartment) (a : characterLattice B.S) (r : ℝ) :
    B.filtration x a r ≤ B.rootGroup a :=
  B.apartment.filtration_le_rootGroupPoints x a r

/-- `U_{a,x,r+} = ⋃_{s>r} U_{a,x,s} = {u ∈ U_a(F) | x_a(u) > r}` (KP Definition 6.1.2). -/
abbrev filtrationPlus (x : B.Apartment) (a : characterLattice B.S) (r : ℝ) :
    Subgroup (rationalPoints G) :=
  B.apartment.filtrationPlus x a r

/-- `U_{2a}(F)`, with `U_{2a}(F) = {1}` if `2a` is not a root. -/
abbrev doubleRootGroup (a : characterLattice B.S) : Subgroup (rationalPoints G) :=
  doubleRootGroupPoints B.i a

/-- The affine root group `U_ψ` of an affine function `ψ` with derivative `a`
(KP Definition 6.3.1). -/
abbrev affineRootGroup (a : characterLattice B.S) (ψ : B.Apartment →ᵃ[ℝ] ℝ) :
    Subgroup (rationalPoints G) :=
  B.apartment.affineRootGroup a ψ

/-- The affine roots `Ψ` of KP Definition 6.3.4, affine functions on the apartment. -/
abbrev affineRoots : Set (B.Apartment →ᵃ[ℝ] ℝ) :=
  B.apartment.affineRoots

/-! ### Facets, chambers, vertices and special points of the building -/

/-- A facet of `B(G)`: a `G(F)`-translate of the image of a facet of the apartment for its
affine roots (KP Proposition 7.6.3 and Remark 7.6.5). -/
def IsFacet (Y : Set B.ReducedBuilding) : Prop :=
  ∃ (g : rationalPoints G) (Fa : Set B.Apartment),
    AffineRootSystem.IsFacet B.affineRoots Fa ∧ Y = (fun x => g • B.apartmentMap x) '' Fa

/-- A chamber of `B(G)`: a `G(F)`-translate of the image of a chamber of the apartment. -/
def IsChamber (Y : Set B.ReducedBuilding) : Prop :=
  ∃ (g : rationalPoints G) (Ca : Set B.Apartment),
    AffineRootSystem.IsChamber B.affineRoots Ca ∧ Y = (fun x => g • B.apartmentMap x) '' Ca

/-- A vertex of `B(G)`: a `G(F)`-translate of the image of a vertex of the apartment. -/
def IsVertex (y : B.ReducedBuilding) : Prop :=
  ∃ (g : rationalPoints G) (x : B.Apartment),
    g • B.apartmentMap x = y ∧ AffineRootSystem.IsVertex B.affineRoots x

/-- A special point of `B(G)` (KP Definition 1.3.39 in some apartment `g · A(S)`). -/
abbrev IsSpecialPoint (y : B.ReducedBuilding) : Prop :=
  B.apartment.IsSpecialBuildingPoint y

theorem isFacet_image {Fa : Set B.Apartment} (h : AffineRootSystem.IsFacet B.affineRoots Fa) :
    B.IsFacet (B.apartmentMap '' Fa) :=
  ⟨1, Fa, h, by simp only [one_smul]⟩

theorem IsFacet.smul {Y : Set B.ReducedBuilding} (hY : B.IsFacet Y) (g : rationalPoints G) :
    B.IsFacet ((g • ·) '' Y) := by
  obtain ⟨h, Fa, hF, rfl⟩ := hY
  refine ⟨g * h, Fa, hF, ?_⟩
  rw [Set.image_image]
  simp only [mul_smul]

theorem isChamber_image {Ca : Set B.Apartment}
    (h : AffineRootSystem.IsChamber B.affineRoots Ca) : B.IsChamber (B.apartmentMap '' Ca) :=
  ⟨1, Ca, h, by simp only [one_smul]⟩

theorem IsChamber.smul {Y : Set B.ReducedBuilding} (hY : B.IsChamber Y) (g : rationalPoints G) :
    B.IsChamber ((g • ·) '' Y) := by
  obtain ⟨h, Ca, hC, rfl⟩ := hY
  refine ⟨g * h, Ca, hC, ?_⟩
  rw [Set.image_image]
  simp only [mul_smul]

theorem isVertex_apartmentMap {x : B.Apartment} (h : AffineRootSystem.IsVertex B.affineRoots x) :
    B.IsVertex (B.apartmentMap x) :=
  ⟨1, x, one_smul _ _, h⟩

theorem IsVertex.smul {y : B.ReducedBuilding} (hy : B.IsVertex y) (g : rationalPoints G) :
    B.IsVertex (g • y) := by
  obtain ⟨h, x, rfl, hx⟩ := hy
  exact ⟨g * h, x, mul_smul g h _, hx⟩

/-! ### Fixers and compact stabilizers -/

/-- The full fixer `G(F)_y` of a point of `B(G)`. -/
abbrev fixer (y : B.ReducedBuilding) : Subgroup (rationalPoints G) :=
  B.apartment.reducedFixer y

/-- The pointwise fixer in `G(F)` of a subset of `B(G)`. -/
abbrev pointwiseFixer (Y : Set B.ReducedBuilding) : Subgroup (rationalPoints G) :=
  B.apartment.pointwiseFixer Y

/-- `U_{a,Ω,0} = U_a(F) ∩ ⋂_{x ∈ Ω} U_{a,x,0}` for `Ω ⊆ A(S)` (KP Definition 7.4.1(1)). -/
abbrev rootFixer (a : characterLattice B.S) (Ω : Set B.Apartment) :
    Subgroup (rationalPoints G) :=
  B.apartment.rootFixer a Ω

/-- `U_{a,Ω,0+} = U_a(F) ∩ ⋂_{x ∈ Ω} U_{a,x,0+}` for `Ω ⊆ A(S)`, the positive-depth analogue
of KP Definition 7.4.1(1). -/
abbrev rootFixerPlus (a : characterLattice B.S) (Ω : Set B.Apartment) :
    Subgroup (rationalPoints G) :=
  B.apartment.rootFixerPlus a Ω

theorem rootFixerPlus_le_rootFixer (a : characterLattice B.S) (Ω : Set B.Apartment) :
    B.rootFixerPlus a Ω ≤ B.rootFixer a Ω :=
  B.apartment.rootFixerPlus_le_rootFixer a Ω

/-- `G(F)^♯_Ω`, generated by the `U_{a,Ω,0}` (KP Definition 7.4.1(2)). -/
abbrev sharpFixer (Ω : Set B.Apartment) : Subgroup (rationalPoints G) :=
  B.apartment.sharpFixer Ω

/-- `K_y = G(F)^1 ∩ G(F)_y` (KP Theorem 4.2.15). -/
abbrev compactStabilizer (y : B.ReducedBuilding) : Subgroup (rationalPoints G) :=
  B.apartment.compactStabilizer y

theorem mem_fixer {y : B.ReducedBuilding} {g : rationalPoints G} : g ∈ B.fixer y ↔ g • y = y :=
  B.apartment.mem_reducedFixer

theorem mem_compactStabilizer {y : B.ReducedBuilding} {g : rationalPoints G} :
    g ∈ B.compactStabilizer y ↔ g ∈ rationalCommonNormKernel G ∧ g • y = y :=
  B.apartment.mem_compactStabilizer

theorem compactStabilizer_le_fixer (y : B.ReducedBuilding) : B.compactStabilizer y ≤ B.fixer y :=
  B.apartment.compactStabilizer_le_reducedFixer y

theorem sharpFixer_le_fixer (x : B.Apartment) :
    B.sharpFixer {x} ≤ B.fixer (B.apartmentMap x) :=
  B.apartment.sharpFixer_le_reducedFixer x

/-! ### The action of `Z(F)` -/

/-- KP's translation `ν : Z(F) → V(S)`, `ν(z) = -ω_Z(z)` (KP Axiom 4.1.4 (A 1)). -/
abbrev translation : rationalPoints B.centralizer.Z →* Multiplicative (V B.S) :=
  B.centralizer.translation

/-- `z ∈ Z(F)` acts on the image of the apartment by the translation by `ν(z)`
(KP Axiom 4.1.4 (A 1) and Proposition 6.2.4). -/
theorem centralizer_smul_apartmentMap (z : rationalPoints B.centralizer.Z) (x : B.Apartment) :
    rationalPoints.map B.centralizer.j z • B.apartmentMap x =
      B.apartmentMap
        ((Submodule.Quotient.mk (B.translation z).toAdd : TranslationSpace B.i) +ᵥ x) := by
  rw [← coe_centralizerToNormalizer B.centralizer.isRepresentedBy z,
    normalizer_smul_apartmentMap]
  exact congrArg B.apartmentMap (B.isOmegaCompatible.smul_eq_vadd z x)

/-- `j(Z(F)^1) ⊆ K_x` for every point `x` of the apartment. -/
theorem map_mem_compactStabilizer {z : rationalPoints B.centralizer.Z}
    (hz : z ∈ rationalCommonNormKernel B.centralizer.Z) (x : B.Apartment) :
    rationalPoints.map B.centralizer.j z ∈ B.compactStabilizer (B.apartmentMap x) :=
  B.isOmegaCompatible.map_mem_compactStabilizer hz x

end ValuationBuildingData

end Langlands.Geometry.Building
