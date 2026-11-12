# The comparisons of Axiom 4.1.1 for all supplied valuation data

`Langlands.Geometry.Building.BuildingComparisonAxiomStatement` is a
Prop-valued `def` at every universe `u`. It asserts the comparisons between
groups in Kaletha–Prasad Axiom 4.1.1 for the existing buildings of arbitrary
supplied valuation data, over a nonarchimedean local field. The module
supplies no proof.

## Statement

The proposition quantifies over every nonarchimedean local field `F`, of
either characteristic, and asserts the conjunction of three clauses. In each
clause `B(H)` denotes the existing quotient `B.ReducedBuilding` of a supplied
`B : ValuationBuildingData H`, with its existing action of `H(F)`. Such data
consist of a maximal split torus `S` of `H`, the class `A(S)` of valuations of
the root datum of `(H, S)` normalized by the valuation of `F`, the actual
centralizer of `S` and axiom V 6 on its rational points. Connected
reductivity of `H` is a field of the data.

1. **Central quotients.** For all group schemes `G`, `G'` over `Spec F` with
   affine structure morphisms, every homomorphism `f : G → G'` with
   `IsCentralSurjection f` (surjective on underlying schemes, with central
   kernel), and all data `B` for `G` and `B'` for `G'`, there is
   `Φ : B(G) ≃ B(G')` with
   `ValuationBuildingData.IsEquivariantBuildingIso B B' (rationalPoints.map f) Φ`.
2. **Derived subgroup.** For all `G`, `G_der` with affine structure morphisms,
   every `d : G_der → G` with `IsDerivedSubgroup d`, and all data `B` for
   `G_der` and `B'` for `G`, there is `Φ : B(G_der) ≃ B(G)` with
   `IsEquivariantBuildingIso B B' (rationalPoints.map d) Φ`.
3. **Simply connected cover.** For all `G`, `G_der`, `G_sc` (affine structure
   morphisms on `G` and `G_sc`), all `d : G_der → G` and `π : G_sc → G_der`
   with `IsSimplyConnectedDerivedCover d π`, and all data `B` for `G_sc` and
   `B'` for `G`, there is `Φ : B(G_sc) ≃ B(G)` with
   `IsEquivariantBuildingIso B B' (rationalPoints.map (π ≫ d)) Φ`.

`IsEquivariantBuildingIso B₁ B₂ φ Φ` (module
`Langlands.Geometry.Building.FullValidity.Assignment`) means that `Φ` is an
isomorphism of buildings and `Φ(g · y) = φ(g) · Φ(y)`. An isomorphism of
buildings maps facets onto facets and apartments onto apartments, both ways,
and is an affine isomorphism `A(S₁) → A(S₂)` in the translated apartment
charts (`IsBuildingIso`).

The three clauses are the predicates `HasCentralQuotientComparisons`,
`HasDerivedSubgroupIdentification` and `HasSimplyConnectedCoverIdentification`
of `KPBuildingAssignment`, with the same binders, asserted here for every
choice of data rather than for the data of one assignment. In particular the
statement implies these three fields of
`KPBuildingAssignment.SatisfiesBuildingExistenceAxiom` for every assignment.

## Source correspondence

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

- Axiom 4.1.1, printed pp.157–158 / PDF pp.188–189: "A surjective
  homomorphism `G → G′` with central kernel induces an equivariant
  isomorphism `B(G) → B(G′)`. In particular, the buildings of `G`, `G_ad`,
  `G_der`, and `G_sc`, are canonically identified, and the action of `G(k)`
  on its building factors through `G_ad(k)`."
- For the building of Chapter 7, §7.6, printed p.264 / PDF p.295: "The natural
  maps `G_sc → G_der → G → G_ad` induce maps between the associated Tits
  systems that satisfy the conditions of Lemma 1.4.13. Therefore they induce
  bijections `B(G_sc) → B(G_der) → B(G) → B(G_ad)` (7.6.1)." Remark 7.6.5,
  printed p.266 / PDF p.297, adds that the quotient (7.6.2) "remains
  unchanged if we replace `G` by `G_ad`, or by `G_sc`, or by `G_der`".
- For general `G`, §9.5, printed p.363 / PDF p.394, refers Axiom 4.1.1 to
  Theorem 9.3.21, printed p.342 / PDF p.373.
- Uniqueness: Proposition 6.2.6, printed p.216 / PDF p.247, says that any two
  valuations of the root datum of `(G, S)` compatible with the valuation of
  `k` (V 6) are equipollent. Proposition 4.4.6 and Corollary 4.4.7, printed
  pp.184–185 / PDF pp.215–216, show that a building satisfying the axioms is
  determined as a `G(k)`-set by its apartment.

The authors' corrections of 1 November 2024,
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, PDF
p.27, keep Axiom 4.1.1 in the corrected list of Definition 4.1.26 and do not
change its comparison clause.

## Derived scope and provenance

This is a derived formulation, not a literal transcription.

- **Every choice of data.** KP state the comparisons for the building they
  construct. Here they are asserted for the Library quotients of arbitrary
  supplied `ValuationBuildingData` on both sides, including data with
  different maximal split tori and different centralizer representatives.
  This universal form is what makes the comparisons independent of the
  choices in an assignment. It is expected to hold because the data carry
  full V 6: by Proposition 6.2.6 (published as
  `OmegaCompatibleApartmentUniquenessStatement`, proved by
  `omegaCompatibleApartmentUniqueness`) the apartment class is determined by
  the group and the torus, and maximal split tori are `G(F)`-conjugate. No
  axiom beyond the data is assumed, in particular neither V 7 nor AS 5.
- **Field.** The statement covers nonarchimedean local fields, of mixed and
  equal characteristic. Other fields allowed by KP are not covered.
- **The building.** The buildings are the Library's valuation quotients
  (KP (7.6.2)), with their existing actions.
- **Isomorphisms of buildings.** Following the published definition, the
  comparison maps are isomorphisms of buildings that intertwine the actions
  along the given homomorphism. Canonicity of the identifications is not
  formalized.
- **Adjoint group.** The identification with the building of `G_ad` and the
  factorization of the action through `G_ad(F)` follow from the first clause
  (`SatisfiesBuildingExistenceAxiom.exists_adjointIdentification` and
  `exists_adjointFactorization`).

No existence of valuation data is asserted. For groups without supplied data
the clauses are vacuous. Together with
`IsomorphismCompatibilityAxiomStatement` (Axiom 4.1.17 for all data) and
`GroupAxiomsExistenceStatement` (the one-group clauses), this statement
implies `BruhatTitsAvailabilityStatement` (KP Theorem 9.2.7 with corrected
Definition 4.1.26): choose data for every group and apply
`KPBuildingAssignment.isAvailableFor_iff`.

## Expected proof route (not prescribed)

For the first clause, let `S ⊂ G` and `S' ⊂ G'` be the tori of `B` and `B'`.
The image `f(S)` is a maximal split torus of `G'`, conjugate to `S'` by some
`g' ∈ G'(F)`. Transport `B'` to the torus `f(S)` by the inner automorphism
of `g'` (`ValuationBuildingData.mapIso`,
`reducedBuildingTransportEquivOfMem` in `CrossTorusBuildingComparison`).
Pull the apartment class of the result back along `f`; it is an
`Ω`-compatible class for `(G, S)`, so Proposition 6.2.6 identifies it with
`B.apartment`. Since `f` maps root groups isomorphically, the stabilizers
correspond, and `(g, x) ↦ (f(g), x)` induces the required map of quotients.
Surjectivity uses `G'(F) = f(G(F)^♮) · Z'(F)`, from KP Fact 2.6.22
(`SimplyConnectedCentralizerProductStatement`). The central-isogeny
pullback in `CentralIsogenyApartment` and `CentralIsogenyFullValuation`,
the derived-cover comparison in `DerivedCoverBuildingComparison`, and the
quotient comparison `ValuationBuildingQuotientComparison` contain much of
this argument. The second and third clauses are similar, with `d` and
`π ≫ d` in place of `f`.
