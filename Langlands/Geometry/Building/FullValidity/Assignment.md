# Definition 4.1.26: availability of Bruhat–Tits theory

This module assembles the full corrected KP Definition 4.1.26 from its ten axioms, on actual
building and integral-model data. It is the final unit of task
`129deca1-ce21-411b-9b79-7e94545fe26d`. It contains:

* the supplied data for one group, `KPBuildingDatum`;
* a choice of such data for all groups, `KPBuildingAssignment`;
* the validity predicates `KPBuildingDatum.SatisfiesGroupAxioms`,
  `KPBuildingAssignment.IsAvailableFor` (Definition 4.1.26) and `KPBuildingAssignment.IsValid`;
* the predicates used in them: isomorphisms of buildings, surjections with central kernel,
  isomorphisms of valued fields;
* accessors, the adapter to the Library's partial bundle, and short lemmas that follow directly
  from the definitions.

Nothing here asserts that any predicate holds for given data, or that data or an assignment
exist.

Ambient setting: `F` is a nonarchimedean local field in an arbitrary universe `u`
(`[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`, Mathlib), of
mixed or equal characteristic. Groups are group schemes `G` over `Spec F` with
`[IsAffineHom G.X.hom]`. `IsConnectedReductive G` is the Library's predicate. `G(F)` is
`rationalPoints G`.

Source: T. Kaletha and G. Prasad, *Bruhat–Tits theory: a new approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. Page numbers are PDF pages of that file, with
the printed page in parentheses. The corrections are `kaletha-prasad-2024-corrections` (version
of 1 November 2024).

## The corrected definition

The book's Definition 4.1.26 (PDF 196, p. 165) lists Axioms 4.1.1, 4.1.4, 4.1.9, 4.1.6, 4.1.17,
4.1.20 and 4.1.22. The corrections (PDF 27) replace this list by "Axioms 4.1.1, 4.1.2, 4.1.4,
4.1.6, 4.1.8, 4.1.9, 4.1.16, 4.1.17, 4.1.20, and 4.1.22 hold". `IsAvailableFor` has one field
for each of these ten axioms. Axiom 4.1.27 (unramified descent, PDF 196) is not in the corrected
list and is not included.

## Declarations

All declarations are in the namespace `Langlands.Geometry.Building`.

| Lean declaration | Source | Content |
|---|---|---|
| `IsCentralSurjection f` (structure) | KP Axiom 4.1.1, PDF 188–189 (pp. 157–158) | `f : G → H` is surjective on the underlying schemes and its kernel is central: `IsCentral (kernelι f)`. |
| `isCentralSurjection_of_isAdjointQuotient` (theorem) | | An actual adjoint quotient (Library `IsAdjointQuotient`) is a central surjection. |
| `isCentralSurjection_of_isCentralIsogeny` (theorem) | | A central isogeny (Library `IsCentralIsogeny`) is a central surjection. |
| `IsValuativeRingEquiv σ` | KP Axiom 4.1.17, PDF 193 (p. 162) | `σ : F₁ ≃+* F₂` identifies the valuative relations: `σ a ≤ᵥ σ b ↔ a ≤ᵥ b`. |
| `specMapOfRingEquiv σ` | | `Spec F₂ → Spec F₁`, the morphism induced by `σ`. |
| `coveringPointsMap σ fG` | KP Axiom 4.1.17 | For `fG : G₁ ×_{F₁,σ} F₂ → G₂`, the map `G₁(F₁) → G₂(F₂)`, `g₁ ↦ fG(g₁)`. `coveringPointsMap_apply` unfolds it. |
| `ValuationBuildingData.IsBuildingIso B₁ B₂ Φ` (structure) | see below | `Φ : B(G₁) ≃ B(G₂)` is an isomorphism of buildings. |
| `ValuationBuildingData.IsEquivariantBuildingIso B₁ B₂ φ Φ` | | `IsBuildingIso B₁ B₂ Φ` and `Φ(g · y) = φ(g) · Φ(y)` for a group homomorphism `φ : G₁(F₁) →* G₂(F₂)`. |
| `isBuildingIso_refl`, `IsBuildingIso.trans`, `isEquivariantBuildingIso_refl`, `IsEquivariantBuildingIso.trans` (theorems) | | Identity and composition. |
| `ValuationBuildingData.HasHalfApartmentFixers B` | KP Axiom 4.1.8(1), PDF 191 (p. 160) | For a relative root `a` and `ψ ∈ Ψ` with derivative `a`, `U_ψ` fixes the image of `{x ∈ A(S) \| ψ(x) ≥ 0}` in `B(G)` pointwise. |
| `ValuationBuildingData.hasHalfApartmentFixers` (theorem) | KP Fact 7.6.7 (cited in §4.1.28, PDF 197) | `HasHalfApartmentFixers B` holds for every `B`, by the Library's `affineRootGroup_le_pointwiseFixer`. |
| `ParahoricBuildingData.zeroFixer_le_zeroStabilizer` (theorem) | | The pointwise fixer `P.zeroFixer Ω` lies in the setwise stabilizer `P.zeroStabilizer (image of Ω)` (KP Definition 4.1.3, module `ChamberAxioms`). |
| `ParahoricBuildingData.modelZeroFixer_ofApartment_one` (theorem) | | For non-empty bounded `Ω ⊆ A(S)`, the zero fixer of the model index `BuildingModelIndex.ofApartment 1 Ω` (Axiom 4.1.20) is `P.zeroFixer Ω` (Axiom 4.1.8). |
| `KPBuildingDatum G` (structure) | KP §4.1 | Supplied data for `G` over `F`, see below. |
| `KPBuildingDatum.SatisfiesAffineRootSystemAxiom D` (structure) | KP Axiom 4.1.6, PDF 190–191 (pp. 159–160) | AS 1–AS 6 on `A(S)`. |
| `KPBuildingDatum.SatisfiesRootGroupActionAxiom D` (structure) | KP Axiom 4.1.8, PDF 191 (p. 160), corrections PDF 27 | Parts (1)–(3) on `A(S)`. |
| `KPBuildingDatum.satisfiesRootGroupActionAxiom_iff` (theorem) | | Since (1) always holds, Axiom 4.1.8 is equivalent to (2) and (3). |
| `KPBuildingDatum.SatisfiesGroupAxioms D` (structure) | KP Definition 4.1.26, corrected | The clauses of the ten axioms that concern `G` alone. This is not full validity. |
| `SatisfiesGroupAxioms.satisfiesPartialBuildingAxioms` (theorem) | | Adapter to the Library's `ParahoricBuildingData.SatisfiesPartialBuildingAxioms D.base`. |
| `SatisfiesGroupAxioms.toPartiallyValidParahoricBuildingData` and its `@[simp]` lemma | | The Library's `PartiallyValidParahoricBuildingData G` with underlying data `D.base`. |
| `SatisfiesRootGroupActionAxiom.zeroFixer_le_parahoric` (theorem) | | `G(F)^0_Ω ≤ P_Ω` (the Chapter 7 group `D.base.parahoric Ω`) for non-empty bounded `Ω`. Only the inclusion is stated. |
| `KPBuildingAssignment` (structure) | | For every nonarchimedean local field `F` in universe `u` and every connected reductive `G` over `F`, data `KPBuildingDatum G`. |
| `KPBuildingAssignment.buildingData`, `.building` | | The building data `B` and the reduced building `B(G)` of `G` in the assignment. |
| `KPBuildingAssignment.HasCentralQuotientComparisons` | KP Axiom 4.1.1, PDF 189 (p. 158) | Comparison clause for central surjections out of `G`. |
| `KPBuildingAssignment.HasDerivedSubgroupIdentification` | same | `B(G_der) ≅ B(G)`. |
| `KPBuildingAssignment.HasSimplyConnectedCoverIdentification` | same | `B(G_sc) ≅ B(G)`. |
| `KPBuildingAssignment.SatisfiesBuildingExistenceAxiom` (structure) | KP Axiom 4.1.1, PDF 188–189 | The whole Axiom 4.1.1 for `G`. |
| `SatisfiesBuildingExistenceAxiom.exists_adjointIdentification` (theorem) | same | An adjoint quotient `G → G_ad` gives an equivariant isomorphism `B(G) ≅ B(G_ad)`. |
| `SatisfiesBuildingExistenceAxiom.exists_adjointFactorization` (theorem) | same | The action of `G(F)` on `B(G)` factors through `G_ad(F)`. |
| `KPBuildingAssignment.HasIsomorphismCompatibility` | KP Axiom 4.1.17, PDF 193 (p. 162) | Axiom 4.1.17 for isomorphisms out of `(F, G)`. |
| `KPBuildingAssignment.IsAvailableFor 𝔅 F G hG` (structure) | KP Definition 4.1.26, corrected | Bruhat–Tits theory is available for `G` over `F` in `𝔅`. Ten fields, below. |
| `KPBuildingAssignment.IsValid 𝔅` | | `IsAvailableFor 𝔅 F G hG` for every `F`, `G` and `hG`. |
| `IsAvailableFor.groupAxioms`, `isAvailableFor_iff` (theorems) | | `IsAvailableFor` is equivalent to `SatisfiesGroupAxioms`, the three Axiom 4.1.1 comparison predicates and `HasIsomorphismCompatibility`. |
| `IsAvailableFor.satisfiesPartialBuildingAxioms`, `IsAvailableFor.toPartiallyValidParahoricBuildingData` | | The adapter to the Library's partial bundle on the same data `(𝔅.datum F G hG).base`. |
| `IsAvailableFor.isBuilding`, `IsAvailableFor.bijOn_torusApartment`, `IsAvailableFor.exists_adjointFactorization` (theorems) | KP Axiom 4.1.1 | The polysimplicial complex is a building (KP Definition 1.5.5). Apartments correspond bijectively to maximal split tori. The action factors through `G_ad(F)`. |
| `IsValid.isAvailableFor` (theorem) | | Evaluation of `IsValid`. |

## Supplied data: `KPBuildingDatum G`

The data are the Library objects that the ten axioms talk about, for a single group.

| Field | Type | Used by |
|---|---|---|
| `base` | Library `ParahoricBuildingData G`: the maximal split torus `i : S → G`, the valuations and apartment `A(S)`, the reduced building `B(G)` with its `G(F)`-action, the root groups `U_a`, the affine roots `Ψ ⊆ Ψ′`, `Z(F)^0` and `G(F)^0` (KP Definition 2.6.23) | all axioms |
| `realization` | `PolysimplicialRealization` of `base` (module `Realization`): a polysimplicial complex and a bijection between its facets and the facets `BuildingFacet` of `B(G)` | Axiom 4.1.1 |
| `splitting` | `ApartmentSplitting` of `base` (module `AffineApartment`): the derived subgroup, its maximal split torus `S'` and the split central torus `A_G` | Axiom 4.1.4 |
| `models` | `BuildingModelFamily base.toValuationBuildingData ↥𝒪[F]` (Library module `Langlands.BruhatTits.IntegralModels.ModelFamily`): integral models over the valuation ring `𝒪[F]` of `F` for the non-empty bounded subsets of the apartments `g · A(S)` and the facets of `B(G)`, with their morphisms and integral split tori | Axioms 4.1.20, 4.1.22 |
| `quotients` | `BuildingModelQuotientFamily base.toValuationBuildingData models` (Library module `Langlands.BruhatTits.IntegralModels.FacetAxioms`): the unipotent radicals and reductive quotients of the special fibres of the facet models | Axiom 4.1.22 |
| `rootDatum` | Library `RelativeRootReflectionData base.i`: coroots and reflection representatives of the relative roots | Axiom 4.1.22(6) |

All axioms use the same `base`. So the building, apartment, root groups, tori and fixers in
Axioms 4.1.20 and 4.1.22 are those of Axioms 4.1.1–4.1.16. `models` is indexed by subsets of
`base.ReducedBuilding`, and `quotients` uses the facet models of the same `models`.

## The ten fields of `IsAvailableFor 𝔅 F G hG`

Write `D = 𝔅.datum F G hG`, `B = D.base.toValuationBuildingData` and `P = D.base`.

| Field | Axiom (KP page) | Lean predicate (module) |
|---|---|---|
| `existenceOfBuilding` | 4.1.1, PDF 188–189 (pp. 157–158) | `𝔅.SatisfiesBuildingExistenceAxiom F G hG` (this module). Four fields: `building : B.SatisfiesBuildingAxiom D.realization` (module `Realization`: building in the sense of Definition 1.5.5, polysimplicial action, torus–apartment correspondence, stabilizer `N(F)` of `A(S)`, face relation), `centralQuotients`, `derivedSubgroups`, `simplyConnectedCovers` |
| `boundedSubgroups` | 4.1.2, PDF 189 (p. 158) | `B.HasBoundedOpenStabilizers` (Library `ValuationBuildingData.HasBoundedOpenStabilizers`, an abbreviation of `KPApartmentData.HasBoundedOpenStabilizers`) |
| `affineStructure` | 4.1.4, PDF 189–190 (pp. 158–159) | `B.SatisfiesAffineApartmentAxiom D.splitting` (module `AffineApartment`: A 0, A 1, A 2) |
| `affineRootSystem` | 4.1.6, PDF 190–191 (pp. 159–160) | `D.SatisfiesAffineRootSystemAxiom`, below |
| `rootGroupAction` | 4.1.8, PDF 191 (p. 160) | `D.SatisfiesRootGroupActionAxiom`, below |
| `titsSystem` | 4.1.9, PDF 192 (p. 161), corrections PDF 27 | `P.HasTitsSystem` (module `ChamberAxioms`) |
| `iwahoriDecomposition` | 4.1.16, PDF 193 (p. 162) | `P.HasIwahoriDecomposition` (module `ChamberAxioms`) |
| `isomorphismCompatibility` | 4.1.17, PDF 193 (p. 162) | `𝔅.HasIsomorphismCompatibility F G hG` (this module) |
| `bruhatTitsGroupSchemes` | 4.1.20, PDF 194 (p. 163) | `D.models.SatisfiesModelAxioms P` (Library, `IntegralModels.ModelFamily`) |
| `reductiveQuotients` | 4.1.22, PDF 194–195 (pp. 163–164) | `D.quotients.SatisfiesMorphismAxioms D.rootDatum` (Library, `IntegralModels.FacetAxioms`) |

The modules `Realization`, `AffineApartment` and `ChamberAxioms` are in
`Langlands.Geometry.Building.FullValidity`. Their Markdown files map each clause of Axioms
4.1.1 (one-group part), 4.1.4, 4.1.9 and 4.1.16 to KP. The Library's `ModelFamily.md` and
`FacetAxioms.md` do the same for Axioms 4.1.20 and 4.1.22.

### Axiom 4.1.6: `SatisfiesAffineRootSystemAxiom`

| Field | Clause | Library predicate |
|---|---|---|
| `rootReflections` | AS 1: `m(u)` fixes `H_u` pointwise, for every `u ∈ U_a(F) ∖ {1}` and every factorization `m(u) = u′ u u″` | `ValuationBuildingData.HasRootReflections` |
| `apartmentAxioms` | AS 2–AS 5, with both inclusions of the first sentence of AS 5 and its two equalities (simply connected; quasi-split adjoint) | `ValuationBuildingData.SatisfiesApartmentAxioms`, an abbreviation of `KPApartmentData.SatisfiesApartmentAxioms` |
| `compatibleApartmentFacets` | AS 6: `A(S) → B(G)` is injective, and the facets of `B(G)` that meet its image are the images of the facets of `A(S)` for `Ψ` | `ValuationBuildingData.HasCompatibleApartmentFacets` |

`Ψ′` in the Library is the set of jumps of the root-group filtrations (KP Remark 4.1.7,
Definition 6.3.4). The Library theorem `ValuationBuildingData.reflectionAffineRoots_eq` shows
that it is KP's `{ψ^u_a}` of AS 2. The Library's `ParahoricBuildingAxioms` notes that the
corrected AS 3 (corrections PDF 27, `∪ {1}` in `U_ψ` and `U_ψ+`) holds for its data by
construction. `SatisfiesApartmentAxioms` also contains V 6 and V 7, the compatibility of the
valuations with `ω` and with the topology of `G(F)` (KP, after Definition 6.1.2, PDF 230,
p. 199). The Library builds `A(S)` from these valuations, and KP notes that all valuations
constructed in the book have V 6 and V 7. They come from the Library's data model, not from the
list of Definition 4.1.26.

### Axiom 4.1.8: `SatisfiesRootGroupActionAxiom`

| Field | Clause | Predicate |
|---|---|---|
| `halfApartmentFixers` | (1): `U_ψ` fixes `A_{ψ ≥ 0}` pointwise | `ValuationBuildingData.HasHalfApartmentFixers` (this module) |
| `zeroFixerGenerators` | (2): `G(F)^0_Ω` is generated by `Z(F)^0` and the `U_ψ` with `ψ ∈ Ψ`, `ψ(Ω) ≥ 0` | `ParahoricBuildingData.HasZeroFixerGenerators` |
| `rootZeroFixers` | (3): `U_a(F) ∩ G(F)^0_Ω = U_ψ` for the smallest `ψ ∈ Ψ′` with derivative `a` that is non-negative on `Ω` | `ParahoricBuildingData.HasRootZeroFixers`. The Library lemma `HasRootZeroFixers.rootGroup_inf_zeroFixer_eq` gives KP's literal form. |

The corrections (PDF 27) require `Ω` to be non-empty and bounded in (2). The Library predicates
for (2) and (3) assume this. `G(F)^0_Ω` is the Library's `zeroFixer`, the elements of `G(F)^0`
that fix the image of `Ω` pointwise (KP §4.1, before Axiom 4.1.8, PDF 191). Part (1) holds for
all data, because the Library's root groups and building are those of KP Chapters 6–7, where it
is KP Fact 7.6.7. The field is kept so that each axiom has its own field.

### Axiom 4.1.1: comparisons and identifications

KP (PDF 189): "A surjective homomorphism `G → G′` with central kernel induces an equivariant
isomorphism `B(G) → B(G′)`. In particular, the buildings of `G`, `G_ad`, `G_der`, and `G_sc`,
are canonically identified, and the action of `G(k)` on its building factors through
`G_ad(k)`."

* `centralQuotients : 𝔅.HasCentralQuotientComparisons F G hG`. For every connected reductive
  `G′` over `F` and every `f : G → G′` with `IsCentralSurjection f`, there is
  `Φ : B(G) ≃ B(G′)` with `IsEquivariantBuildingIso B(G) B(G′) (rationalPoints.map f) Φ`.
  `IsCentralSurjection` is KP's wording: `surjective` (the morphism of schemes is surjective)
  and `isCentral_kernelι` (the actual kernel `kernelι f : ker f → G` is central, Library
  `IsCentral`).
* `derivedSubgroups : 𝔅.HasDerivedSubgroupIdentification F G hG`. For every actual derived
  subgroup `d : G_der → G` (Library `IsDerivedSubgroup`) with `G_der` connected reductive, there
  is `Φ : B(G_der) ≃ B(G)`, equivariant along `rationalPoints.map d`.
* `simplyConnectedCovers : 𝔅.HasSimplyConnectedCoverIdentification F G hG`. For every
  `d : G_der → G` and `π : G_sc → G_der` with `IsSimplyConnectedDerivedCover d π` (Library) and
  `G_sc` connected reductive, there is `Φ : B(G_sc) ≃ B(G)`, equivariant along
  `rationalPoints.map (π ≫ d)`.
* `G_ad` and the factorization: `exists_adjointIdentification` applies `centralQuotients` to an
  actual adjoint quotient `q : G → G_ad` (Library `IsAdjointQuotient`).
  `exists_adjointFactorization` then defines `ρ(a) = Φ⁻¹ ∘ a ∘ Φ` and proves
  `ρ(q(g)) y = g · y`. These are theorems, not fields.

*Why `G_der` and `G_sc` are fields.* KP presents these identifications as consequences ("In
particular") of the first sentence. `G_der → G` is not surjective, so they are not instances of
the comparison clause for maps out of `G`. They follow from instances for maps out of `G_der` and
`G_sc`, for example `G_der → G_ad` and `G_sc → G_der`, together with `G → G_ad`. The instances
for `G_der` and `G_sc` belong to the availability predicates of those groups. So that
`IsAvailableFor 𝔅 F G hG` contains the whole sentence about `G`, the two identifications are
stated as clauses for `G`. This derivation is not formalized.

*Existence, not canonicity.* The predicates ask for an equivariant isomorphism of buildings.
They do not formalize the words "induces" and "canonically" (functoriality in `f`, uniqueness, or
compatibility among the identifications).

*Maps into `G`.* `IsAvailableFor 𝔅 F G hG` contains the comparison clause for maps out of `G`,
which is KP's sentence for the fixed group `G`. Maps `G′ → G` are covered by
`IsAvailableFor 𝔅 F G′ hG′`. `IsValid 𝔅` contains all of them.

### Isomorphisms of buildings: `IsBuildingIso`

KP uses "isomorphism of buildings" without a separate definition. The predicate is assembled
from the following.

* KP Definition 1.5.1(13) (PDF 86, p. 55) defines isomorphisms of polysimplicial complexes, and
  Definition 1.5.5 (PDF 86–87, pp. 55–56) defines a building as a polysimplicial complex with a
  set of apartments. KP §7.10 (PDF 307, p. 276) warns that an isomorphism of polysimplicial
  complexes need not be an isomorphism of buildings, because the apartments must also match.
* After Remark 4.1.5 (PDF 190, p. 159) KP does not distinguish `B(G)` from its geometric
  realization, in which every apartment carries the affine structure of Axiom 4.1.4.
* The isomorphisms KP constructs are affine on apartments. The proof of Corollary 4.4.5
  (PDF 214–215, pp. 183–184) shows that the isomorphism restricts on each apartment to the
  canonical isomorphism of Proposition 4.4.3 (PDF 212–213, pp. 181–182), which is an
  isomorphism of affine spaces. The proof of Proposition 7.9.5 (PDF 307, p. 276), which proves
  Axiom 4.1.17, restricts its isomorphism to an isomorphism `A(S₁) → A(S₂)`.

`IsBuildingIso B₁ B₂ Φ` is a structure with three fields, for a bijection
`Φ : B₁.ReducedBuilding ≃ B₂.ReducedBuilding`:

| Field | Content |
|---|---|
| `isFacet_image_iff` | `Φ '' Y` is a facet of `B(G₂)` iff `Y` is a facet of `B(G₁)` (Library `ValuationBuildingData.IsFacet`) |
| `isApartment_image_iff` | `Φ '' Y` is an apartment iff `Y` is an apartment (Library `ValuationBuildingData.IsApartment`, the translates `g · A(S)`) |
| `exists_affineEquiv` | for every `g₁ ∈ G₁(F₁)` there are `g₂ ∈ G₂(F₂)` and an affine isomorphism `f : A(S₁) ≃ᵃ[ℝ] A(S₂)` with `Φ(g₁ · x) = g₂ · f(x)` (Library `translatedApartmentMap`) |

Since `Φ` is a bijection, the first field gives a bijection between the facets. An affine
isomorphism of finite-dimensional real affine spaces is a homeomorphism. So, mathematically, `Φ`
also preserves the face relation, which is read in a common apartment (Library
`FacetPrecedes`). This consequence is not formalized.

`IsEquivariantBuildingIso B₁ B₂ φ Φ` adds `Φ(g · y) = φ(g) · Φ(y)`. Comparisons use
`φ = rationalPoints.map f`, and Axiom 4.1.17 uses `φ = coveringPointsMap σ fG`.

### Axiom 4.1.17: `HasIsomorphismCompatibility`

KP (PDF 193, p. 162): for two Henselian valued fields `k₁`, `k₂`, an isomorphism
`f_k : k₁ → k₂`, connected reductive `k_i`-groups `G_i` and an isomorphism
`f_G : G₁ ×_{k₁} k₂ → G₂` of `k₂`-groups, the pair `(f_k, f_G)` induces an isomorphism of
buildings `f_B : B(G₁, k₁) → B(G₂, k₂)` with `f_B(g₁ x₁) = f_G(g₁) f_B(x₁)`.

`𝔅.HasIsomorphismCompatibility F G hG` says: for every nonarchimedean local field `F₂` in
universe `u`, every ring isomorphism `σ : F ≃+* F₂` with `IsValuativeRingEquiv σ`, every
connected reductive `G₂` over `F₂`, and every isomorphism
`fG : (GroupScheme.baseChange (specMapOfRingEquiv σ)).obj G ≅ G₂`, there is
`Φ : B(G) ≃ B(G₂)` with `IsEquivariantBuildingIso B(G) B(G₂) (coveringPointsMap σ fG.hom) Φ`.

* *Fields.* The assignment `𝔅` has buildings only for nonarchimedean local fields in universe
  `u`. Axiom 4.1.17 is therefore stated for these fields. KP's Henselian valued fields are more
  general. This is the scope of the whole assignment, not of this axiom alone.
* *Isomorphism of valued fields.* `IsValuativeRingEquiv σ` says that `σ` identifies the
  valuative relations of `F` and `F₂`. This is the same condition as Mathlib's
  `ValuativeExtension.vle_iff_vle` for an algebra map.
* *The map on points.* `coveringPointsMap σ fG` sends an `F`-point `g` of `G` to the `F₂`-point
  of the base change given by the Library's `baseChangeSectionHom`, and then applies `fG`. This
  is KP's `g₁ ↦ f_G(g₁)`.
* *Source.* `IsAvailableFor 𝔅 F G hG` contains the instances with source `(F, G)`. `IsValid 𝔅`
  contains all instances.
* As for Axiom 4.1.1, the predicate asks for existence. It does not formalize "induces".

### Which tori

The per-torus axioms 4.1.4 (A 1), 4.1.6, 4.1.8, 4.1.9 and 4.1.16 are stated at the base torus
`S` of `P`, as in the earlier units and in the Library's `ParahoricBuildingData`. Other maximal
split tori enter through the torus charts of Axiom 4.1.1 (module `Realization`). The integral
models of Axioms 4.1.20 and 4.1.22 are indexed by the subsets of every apartment `g · A(S)`, with
torus `i ≫ Int(g)` (Library `BuildingModelFamily`).

## Fixers, stabilizers and parahorics

The Library keeps several groups attached to `Ω ⊆ A(S)` apart, and this module does not
identify them.

* `P.zeroFixer Ω`: pointwise fixer in `G(F)^0` (Axioms 4.1.8 and 4.1.20).
* `P.zeroStabilizer Y`: setwise stabilizer in `G(F)^0` (KP Definition 4.1.3, Axioms 4.1.9 and
  4.1.16). `zeroFixer_le_zeroStabilizer` gives one inclusion.
* `P.parahoric Ω`: the Chapter 7 group `Z(F)^0 · G(F)^♯_Ω` (KP Definition 7.4.1).
  `SatisfiesRootGroupActionAxiom.zeroFixer_le_parahoric` gives `zeroFixer ≤ parahoric` under
  Axiom 4.1.8 (2). Equality is not asserted.
* `BuildingModelFamily.zeroFixer P Ω`: the zero fixer used by Axiom 4.1.20, for a model index
  `Ω`. `modelZeroFixer_ofApartment_one` shows that it is `P.zeroFixer Ω` on the index of `Ω`
  in the chart `g = 1`.

## Interfaces

* `SatisfiesGroupAxioms D` collects the nine fields of `IsAvailableFor` that concern `G` alone.
  The `building` field is `B.SatisfiesBuildingAxiom D.realization`, the one-group part of Axiom
  4.1.1. It leaves out the Axiom 4.1.1 comparisons and Axiom 4.1.17, which involve other groups.
  `isAvailableFor_iff` states the decomposition.
* The adapter `IsAvailableFor.satisfiesPartialBuildingAxioms` gives the Library's
  `ParahoricBuildingData.SatisfiesPartialBuildingAxioms` on the same data `D.base`. Its fields
  come from AS 1–AS 6, the stabilizer clause of Axiom 4.1.1
  (`SatisfiesBuildingAxiom.normalizerApartmentStabilizer`), Axiom 4.1.2 and Axiom 4.1.8 (2),
  (3).
* Downstream statements use `IsAvailableFor 𝔅 F G hG` or `IsValid 𝔅` as hypotheses on an
  assignment `𝔅`, and reach the components through the fields and `D = 𝔅.datum F G hG`.

The Library statements that earlier units cite as unproved inputs, such as
`MaximalSplitTorusConjugacyStatement`, are discussed in `Realization.md` and `AffineApartment.md`.
This module adds none.
