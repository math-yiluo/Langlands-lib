# Unions of closed facets of the actual KP quotient are closed

`Langlands.Geometry.Building.FacetClosureUnionClosedStatement` is a
Prop-valued `def` at every universe `u`. It states the second assertion of
Kaletha–Prasad Theorem 4.2.10 for the existing quotient of supplied valuation
building data: for every set of facets of `B(G)`, the union of their closures
is closed. The module supplies no proof.

## Statement

The proposition quantifies over:

- every nonarchimedean local field `F`, of mixed or equal characteristic
  (`[Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]`);
- every group scheme `G` over `Spec F` with `[IsAffineHom G.X.hom]`;
- supplied `B : ValuationBuildingData G` (its field `isConnectedReductive`
  makes `G` connected reductive);
- every metric on the existing quotient `B.ReducedBuilding` for which the
  existing action of `rationalPoints G` is isometric
  (`[MetricSpace B.ReducedBuilding]
  [IsIsometricSMul (rationalPoints G) B.ReducedBuilding]`).

Its premises are:

1. `∀ x : B.ReducedBuilding, B.HasCommonApartmentWith x`: any two points lie
   in a common apartment `g · A(S)`;
2. `B.SatisfiesApartmentAxioms`: the Library's conditions V 6, V 7 and
   AS 2–AS 5 on the apartment class `A(S)` of the supplied data
   (`KPApartmentData.SatisfiesApartmentAxioms`). V 6 is already part of `B`
   (its field `isOmegaCompatible`), so by
   `ValuationBuildingData.satisfiesApartmentAxioms_iff` the premise asks
   for V 7 and AS 2–AS 5. Here V 7 (KP Definition 6.1.2) says: for every
   valuation in the class and every relative root `a`, the filtration
   subgroups `U_{a,r}` (`r ∈ ℝ`) are open in `U_a(F)`, bounded in `G(F)` in
   the sense of KP Definition 2.2.1, and form a neighbourhood base of `1` in
   `U_a(F)`, for the published topology on `G(F)`. AS 2–AS 5 (KP
   Axiom 4.1.6) say that the extended affine roots `Ψ′` and the affine roots
   `Ψ` are affine root systems with gradient root system `Φ`, that every
   element of `Ψ′` lies in `Ψ` or has its double in `Ψ`, and that the image
   of `N(F)` acting on `A(S)` lies between the affine Weyl group and the
   extended affine Weyl group of `Ψ`, with the stated equalities for simply
   connected and for quasi-split adjoint `G`;
3. `Isometry B.apartmentMap`: the apartment map `A(S) → B(G)` is an
   isometry, where `A(S)` carries the Euclidean root metric of
   `Langlands.Geometry.Building.ValuationApartmentMetric` (the module
   installs `apartmentMetricSpace` and its companions as local instances).

These are exactly the hypotheses of the published completeness theorem
`ValuationBuildingData.completeSpace_of_isometry_apartmentMap_of_satisfiesApartmentAxioms`,
which formalizes the first assertion of the same theorem.

The conclusion is: for every `X : Set (Set B.ReducedBuilding)` with
`B.IsFacet Y` for all `Y ∈ X`,

```
IsClosed (⋃ Y ∈ X, closure Y)
```

in the topology of the given metric. Here `B.IsFacet Y` means that `Y` is a
`G(F)`-translate of the image of a facet of `A(S)` for its affine roots
(`ValuationBuildingData.IsFacet`), and `closure Y` is the topological closure.
The set `X` is arbitrary: it may be infinite, and the building need not be
locally finite.

## Source correspondence

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
Theorem 4.2.10, printed pp.171–172 / PDF pp.202–203. KP state: "The metric
space B is complete. If X is a set of facets, then ⋃_{F∈X} F̄ is closed."
The overbar denotes the closure of each facet. KP prove the second assertion
for a general, not necessarily locally finite, building, using Lemma 4.2.11
(printed pp.171–172).

The standing hypotheses of Section 4.2 (printed p.168 / PDF p.199) are a
building satisfying Axioms 4.1.1, 4.1.2, 4.1.4 and 4.1.9, with the metric `d`
of Proposition 4.2.1: the unique function whose restriction to every
apartment is the Euclidean metric for a chosen Weyl-invariant compatible
system of metrics. The authors' corrections of 1 November 2024,
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp.28–29, add Axiom 4.1.6 to those hypotheses and make the metric of
Proposition 4.2.1 `G`-invariant.

## Derived scope and provenance

This is a derived formulation of the source assertion, not a literal
transcription. It differs from the source in the following ways.

- **Field.** KP work over a discretely valued field with Henselian valuation
  ring and perfect residue field. The statement covers nonarchimedean local
  fields of either characteristic, which are of that kind.
- **Building.** The building is the existing quotient of supplied
  `ValuationBuildingData`, and facets are the existing `IsFacet` sets. No
  existence of the data or of the hypotheses is asserted. Existence is the
  separate target `RootValuationBuildingConstructionStatement`.
- **Metric.** The source metric is characterized by its restriction to every
  apartment being Euclidean. Premises 1 and 3 and the isometric action say
  that the given metric restricts to the Euclidean root metric on every
  apartment `g · A(S)`, and any two points lie in one apartment. By the
  argument of Proposition 4.2.1 the metric is therefore the source metric
  `d` for the Weyl-invariant normalization of `ValuationApartmentMetric`.
  KP allow any Weyl-invariant normalization; other normalizations are not
  covered by this statement.
- **Axioms.** Instead of the corrected list 4.1.1, 4.1.2, 4.1.4, 4.1.6 and
  4.1.9, the statement assumes only the three premises above, as the
  published completeness theorem does. Premise 2 contains one condition
  that is not among the standing hypotheses of Section 4.2: the topology
  compatibility V 7 of KP Definition 6.1.2 (printed p.199 / PDF p.230),
  which KP introduce for valuations of root data in Chapter 6 and which,
  as they note there, holds for all valuations constructed in the book.
  The statement therefore assumes V 7 in addition to the source
  hypotheses of Theorem 4.2.10, so it is weaker than the source in this
  respect; premise 2 is kept as in the published completeness theorem
  rather than weakened. The source's use of Axiom 4.1.6 in
  Lemma 4.2.11 (discreteness of parallel affine-root hyperplanes) is covered
  by the local finiteness contained in `SatisfiesApartmentAxioms`. The
  source's use of Propositions 1.5.13 and 1.5.14 (moving a facet into a
  fixed apartment by an element fixing the given point) is replaced by the
  common-apartment premise and the quotient presentation of
  `ReducedBuilding`.

The intended proof follows the source. Lemma 4.2.11 gives, for each point
`x`, a ball around `x` such that every facet meeting the ball contains `x` in
its closure. If `x` is in the closure of the union, the ball meets the
closure of some facet in `X`, hence meets that facet, so `x` lies in its
closure. The first assertion of Theorem 4.2.10, completeness, is already
published as the theorem cited above and is not repeated here.
