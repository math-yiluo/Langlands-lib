# Axiom 4.1.17 for all supplied valuation data

`Langlands.Geometry.Building.IsomorphismCompatibilityAxiomStatement` is a
Prop-valued `def` at every universe `u`. It asserts Kaletha–Prasad Axiom
4.1.17 (compatibility with isomorphisms) for the existing buildings of
arbitrary supplied valuation data over nonarchimedean local fields. The module
supplies no proof.

## Statement

The proposition quantifies over:

- two nonarchimedean local fields `F₁`, `F₂` in the same universe, of either
  characteristic;
- a ring isomorphism `σ : F₁ ≃+* F₂` with `IsValuativeRingEquiv σ`, that is,
  `σ a ≤ᵥ σ b ↔ a ≤ᵥ b` for all `a, b`: an isomorphism of valued fields;
- group schemes `G₁` over `Spec F₁` and `G₂` over `Spec F₂` with affine
  structure morphisms, and an isomorphism of `F₂`-groups
  `f_G : G₁ ×_{F₁,σ} F₂ ≅ G₂`, where the base change is along
  `specMapOfRingEquiv σ : Spec F₂ → Spec F₁`;
- arbitrary data `B₁ : ValuationBuildingData G₁` and
  `B₂ : ValuationBuildingData G₂`. Such data consist of a maximal split torus,
  the class of valuations of the root datum normalized by the valuation of the
  field, the actual centralizer of the torus and axiom V 6 on its rational
  points. Connected reductivity of the group is a field of the data.

It asserts that there is `Φ : B₁.ReducedBuilding ≃ B₂.ReducedBuilding` with
`ValuationBuildingData.IsEquivariantBuildingIso B₁ B₂ (coveringPointsMap σ f_G.hom) Φ`.
Here `coveringPointsMap σ f_G.hom : G₁(F₁) → G₂(F₂)` sends `g₁` to `f_G(g₁)`,
the image under `f_G` of the `F₂`-point of the base change given by `g₁`.
`IsEquivariantBuildingIso` (module
`Langlands.Geometry.Building.FullValidity.Assignment`) means that `Φ` is an
isomorphism of buildings (facets onto facets and apartments onto apartments,
both ways, affine in the translated apartment charts) and
`Φ(g₁ · y) = f_G(g₁) · Φ(y)`.

This is the predicate `KPBuildingAssignment.HasIsomorphismCompatibility`,
with the same binders, asserted for every choice of data rather than for the
data of one assignment. In particular the statement implies the field
`isomorphismCompatibility` of `KPBuildingAssignment.IsAvailableFor` for every
assignment.

## Source correspondence

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

- Axiom 4.1.17, printed p.162 / PDF p.193: "Consider two Henselian valued
  fields `k₁` and `k₂` and an isomorphism `f_k : k₁ → k₂`. Let `G_i` be a
  connected reductive `k_i`-group and let `f_G : G₁ → G₂` be an isomorphism
  covering `f_k`; that is, `f_G : G₁ ×_{k₁} k₂ → G₂` is an isomorphism of
  `k₂`-groups. The pair `(f_k, f_G)` induces an isomorphism of buildings
  `f_B : B(G₁, k₁) → B(G₂, k₂)`. It satisfies `f_B(g₁x₁) = f_G(g₁)f_B(x₁)` for
  `g₁ ∈ G₁(k₁)` and `x₁ ∈ B(G₁, k₁)`."
- Proposition 7.9.5, printed p.276 / PDF p.307, proves the same assertion for
  the building of Chapter 7, via the parahoric subgroups. KP 4.1.28, printed
  p.166 / PDF p.197, cites it for Axiom 4.1.17. §9.5, printed p.363 / PDF
  p.394, cites it for general `G`.
- Uniqueness: Proposition 6.2.6, printed p.216 / PDF p.247, says that any two
  valuations of the root datum of `(G, S)` compatible with the valuation of
  `k` (V 6) are equipollent.

The authors' corrections of 1 November 2024,
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, PDF
p.27, keep Axiom 4.1.17 in the corrected list of Definition 4.1.26 and do not
change it.

## Derived scope and provenance

This is a derived formulation, not a literal transcription.

- **Every choice of data.** KP state the axiom for the buildings they
  construct. Here it is asserted for the Library quotients of arbitrary
  supplied `ValuationBuildingData` on both sides, with arbitrary maximal split
  tori and centralizer representatives. It is expected to hold because the
  data carry full V 6, so Proposition 6.2.6 (published as
  `OmegaCompatibleApartmentUniquenessStatement`, proved by
  `omegaCompatibleApartmentUniqueness`) determines the apartment class from
  the group and the torus, and an isomorphism of valued fields preserves the
  normalized valuation `localFieldOrder`. No axiom beyond the data is assumed,
  in particular neither V 7 nor AS 5.
- **Fields.** KP allow Henselian valued fields. The statement covers
  nonarchimedean local fields in one universe, as in the published
  `HasIsomorphismCompatibility`. Valued-field isomorphisms are ring
  isomorphisms preserving the valuative relation; no compatibility with the
  topologies is required beyond what this implies.
- **Isomorphisms of buildings.** Following the published definition, `f_B` is
  an isomorphism of buildings intertwining the actions along `f_G`. Its
  canonicity, and functoriality in the pair `(f_k, f_G)`, are not formalized.

No existence of valuation data is asserted. For groups without supplied data
the statement is vacuous. Together with `BuildingComparisonAxiomStatement`
(the comparisons of Axiom 4.1.1 for all data) and
`GroupAxiomsExistenceStatement` (the one-group clauses), this statement
implies `BruhatTitsAvailabilityStatement` (KP Theorem 9.2.7 with corrected
Definition 4.1.26).

## Expected proof route (not prescribed)

Transport `B₁` along `(σ, f_G)` to data for `G₂` with torus the image of the
torus of `B₁`. The transported valuations are normalized by the transported
order on `F₂`, which equals `localFieldOrder F₂` because `σ` preserves the
valuative relation. Proposition 6.2.6 and conjugacy of maximal split tori then
identify the transported data with `B₂` up to the cross-torus transport
already in the Library (`CrossTorusBuildingComparison`,
`ValuationBuildingData.mapIso`, `ValuationBuildingQuotientComparison`). The
existing transports handle a group isomorphism over one field; the new step
is the change of field along `σ`.
