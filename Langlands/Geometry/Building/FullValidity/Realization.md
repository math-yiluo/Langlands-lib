# Axiom 4.1.1 for one group on the reduced building

This module states the clauses of KP Axiom 4.1.1 that concern a single group `G`. They are
stated on the actual reduced building of the Library's valuation building data. It is the first
building-side unit of the full corrected Definition 4.1.26 predicate (task
`129deca1-ce21-411b-9b79-7e94545fe26d`). It contains definitions, one structure of validity
clauses and short intrinsic lemmas. It does not assert that the clauses hold for any data, or
that data exist.

Ambient setting: `F` is a nonarchimedean local field in an arbitrary universe `u`
(`[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`), in mixed or
equal characteristic. `G` is a group scheme over `Spec F` with `[IsAffineHom G.X.hom]`, and
`B : ValuationBuildingData G` is the Library's building datum. It contains the maximal split
torus `i : S → G` (`B.i`, with `B.isMaximalSplitTorus`), the connected-reductive hypothesis
`B.isConnectedReductive`, the apartment `A(S)` (`B.Apartment`) and the reduced building
`B(G) = B.ReducedBuilding`. `B(G)` is the quotient (7.6.2) of `G(F) × A(S)` from KP
Remark 7.6.5.

Source: T. Kaletha and G. Prasad, *Bruhat–Tits theory: a new approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. Page numbers are PDF pages of that file, with the
printed page in parentheses. The 2024 corrections (`kaletha-prasad-2024-corrections`) do not
change Axiom 4.1.1. They add "(B(G) as in Axiom 4.1.1)" to Axiom 4.1.9 (corrections PDF 27),
which is why the building of Axiom 4.1.1 must be the actual reduced building used by the other
axioms.

## Supplied data and validity clauses

Supplied data:

* `B : ValuationBuildingData G` (Library, `Langlands.Geometry.Building.ValuationBuildingData`).
  It supplies the reduced building, the apartment `A(S)`, its image
  `B.apartmentImage = Set.range B.apartmentMap`, the `G(F)`-action and the facets
  `ValuationBuildingData.IsFacet`.
* `R : B.PolysimplicialRealization`. It consists of a finite index type `R.index`, vertex types
  `R.V i`, a polysimplicial complex `R.complex : AbstractBuilding.PolysimplicialComplex R.index R.V`
  (KP Definition 1.5.1(2), PDF 85, p. 54) and a bijection
  `R.realize : R.complex.facets ≃ IntegralModels.BuildingFacet B` between the facets of the complex
  and the facets of `B(G)`.

Validity clauses: `B.SatisfiesBuildingAxiom R`, a structure with five fields, and the structure
`B.HasTorusApartmentCorrespondence` with two fields used in it.

## Map of Axiom 4.1.1 (KP PDF 188–189, pp. 157–158)

| Source sentence | Lean |
|---|---|
| "There exists a building `B = B(G)` in the sense of Definition 1.5.5" (PDF 188) | The data `R`. The field `SatisfiesBuildingAxiom.isBuilding : AbstractBuilding.IsBuilding R.complex R.apartments` covers KP Definition 1.5.5 (PDF 86–87, pp. 55–56), axioms BL 1–BL 4. The apartments `R.apartments` are the sets of facets of `K` realized inside an apartment `g · A(S)` of `B(G)` (`PolysimplicialRealization.apartmentComplex`). |
| The polysimplicial complex `B(G)` is the reduced building with its facets and face relation. KP does not distinguish `B(G)` from its geometric realization (after Remark 4.1.5, PDF 190). The face relation `F ≺ F'` comes from Notation 1.3.34 (paragraph after Axiom 4.1.1, PDF 189). | `R.realize` and the field `faceCompatible : R.IsFaceCompatible`. For facets of `K`, `F ⊆ F'` holds if and only if `IntegralModels.FacetPrecedes B (R.realize F) (R.realize F')`. Facets of `B(G)` are `IntegralModels.BuildingFacet B`. `FacetPrecedes` is the face relation read in a common translated apartment. Both are the Library definitions (module `Langlands.BruhatTits.IntegralModels.FacetParabolicOrder`) that the integral-model Axioms 4.1.20 and 4.1.22 use. |
| "equipped with an action of `G(k)` by polysimplicial automorphisms" (PDF 188) | Field `polysimplicialAction : R.IsPolysimplicialAction`. For each `g ∈ G(F)` there is a polysimplicial automorphism `e` of `K` (`AbstractBuilding.IsPolysimplicialAutomorphism`, KP Definition 1.5.1(13), PDF 86) such that `e` maps a facet `F` to `F'` exactly when `g` maps the realized facet of `F` onto that of `F'`. The action on `B(G)` is the Library action of `G(F)` on the reduced building. |
| "The apartments of this building are in bijective `G(k)`-equivariant correspondence with the maximal split tori of `G`" (PDF 188) | Field `torusApartmentCorrespondence : B.HasTorusApartmentCorrespondence`, explained below. |
| "In particular, the stabilizer in `G(k)` of an apartment `A = A(S)` … is `N(k)`" (PDF 188) | Field `normalizerApartmentStabilizer : B.HasNormalizerApartmentStabilizer`. This is the Library clause `MulAction.stabilizer (rationalPoints G) B.apartmentImage = normalizerPoints B.i`. KP derives it from the correspondence, but it is kept as a field. It is also a field of the Library's partial bundle `ParahoricBuildingData.SatisfiesPartialBuildingAxioms`. |
| "A surjective homomorphism `G → G'` with central kernel induces an equivariant isomorphism `B(G) → B(G')`. In particular, the buildings of `G`, `G_ad`, `G_der`, and `G_sc` are canonically identified, and the action of `G(k)` on its building factors through `G_ad(k)`." (PDF 189) | Not in this module. These sentences compare the buildings of two groups. A later unit of this task states them on families of building data over all groups. |

## The torus–apartment correspondence

Maximal split tori are compared as subgroup functors of `G`:

* `maximalSplitTori G` is the set of ranges `SubgroupFunctor.range i'` of the maximal split tori
  `i' : S' → G` (`IsMaximalSplitTorus`). A maximal split torus is a closed immersion, so its range
  determines it up to unique isomorphism over `G`.
* `B.conjTorus g = SubgroupFunctor.range (B.i ≫ (G.innerIso g).hom)` is `g S g⁻¹`.
  `conjTorus_mem_maximalSplitTori` shows it is a maximal split torus.
* `B.IsTorusChart i₂ h σ` says that an actual torus `i₂ : T₂ → G` is `h S h⁻¹` through
  `σ : S ≅ T₂`, that is `i ≫ Int(h) = σ ≫ i₂`. `IsTorusChart.conjTorus_eq` gives
  `B.conjTorus h = SubgroupFunctor.range i₂`.

The apartment corresponding to `g S g⁻¹` must be `g · A(S)`. This holds for `g = 1` because `A(S)`
corresponds to `S`, and for other `g` by equivariance. Bijectivity and equivariance then come
down to two clauses, the fields of `HasTorusApartmentCorrespondence`:

* `exists_torusChart`: every actual maximal split torus `i₂ : T₂ → G` has a chart `(h, σ)`. So the
  correspondence is defined on all maximal split tori. This is the `G(F)`-conjugacy of maximal
  split tori. The theorem `exists_torusChart_of_maximalSplitTorusConjugacy` derives it from the
  Library statement `Langlands.GroupScheme.MaximalSplitTorusConjugacyStatement`, which the
  Library does not prove. It is therefore kept as a clause, and it becomes redundant once that
  statement is proved.
* `conjTorus_eq_iff`: `g S g⁻¹ = h S h⁻¹ ↔ g · A(S) = h · A(S)`. So `g S g⁻¹ ↦ g · A(S)` is well
  defined and injective.

Consequences proved here:

* `HasTorusApartmentCorrespondence.exists_conjTorus_eq`: every element of `maximalSplitTori G`
  is some `B.conjTorus g`.
* `B.torusApartment T` is the union of the apartments `g · A(S)` with `B.conjTorus g = T`.
  `torusApartment_conjTorus` gives `torusApartment (conjTorus g) = g · A(S)`, and
  `torusApartment_range` gives that an actual torus with a chart at `h` has apartment
  `h · A(S)`.
* `HasTorusApartmentCorrespondence.bijOn`: `T ↦ B.torusApartment T` is a bijection from
  `maximalSplitTori G` onto the apartments `{Y | B.IsApartment Y}` of `B(G)`. Equivariance holds
  by construction, since `torusApartment (conjTorus (g h)) = g · torusApartment (conjTorus h)`.

The apartments of `B(G)` are the Library's `ValuationBuildingData.IsApartment`, the translates
`g · A(S)` (KP Proposition 7.6.3(1) and Corollary 7.6.9). The charts `IsTorusChart` are also what
Axiom 4.1.4 (A 2) uses to read the apartment of an arbitrary maximal split torus (module
`Langlands.Geometry.Building.FullValidity.AffineApartment`).

## Interfaces to existing objects

* The building is the actual reduced building `B.ReducedBuilding`. It is not a separate abstract
  set. The polysimplicial complex `K` is linked to it by `R.realize` on facets, by
  `faceCompatible` on the face relation, by `polysimplicialAction` on the group action and by
  `R.apartments` on apartments.
* Facets and their order are the Library's `IntegralModels.BuildingFacet` and
  `IntegralModels.FacetPrecedes` (Worker 384's published module). So the facets indexing the
  integral models of Axioms 4.1.20 and 4.1.22 are those of Axiom 4.1.1.
* The stabilizer clause is the existing `ValuationBuildingData.HasNormalizerApartmentStabilizer`,
  unchanged.
* Tori, inner automorphisms and normalizers are the Library's `IsMaximalSplitTorus`,
  `GroupScheme.innerIso`, `SubgroupFunctor.range` and `normalizerPoints`.

## Design notes

* The axiom is stated at the base torus `S` of `B`. Every other maximal split torus enters through
  a chart `(h, σ)`, and its apartment is `h · A(S)`. This is how the Library's reduced building
  is built (KP §7.6).
* KP Definition 1.5.5 allows a polysimplicial complex, not only a simplicial one, which matters
  for non-simple `G`. That is why `K` is a polysimplicial complex with finitely many factors.
