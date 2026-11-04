# Point-preserving facet parahoric identifications

This internal helper constructs `KPApartmentData.sharpFacetEquivAt` and
`ParahoricBuildingData.parahoricFacetEquivAt`. They identify the actual sharp
facet subgroup and full facet parahoric, respectively, with the corresponding
group at any chosen point of the facet. Both multiplicative equivalences
preserve the underlying rational point.

The sharp construction works over an arbitrary field at universe `u` with
the published `KPApartmentData i ω`, monomorphism and affine-group hypotheses.
Its only additional apartment premise is AS 4, written explicitly as the
condition that every extended affine root or its double is an affine root.
The full construction uses every actual `P : ParahoricBuildingData G`, at
arbitrary universe `u`, with its unchanged field and group instances, and
assumes `P.apartment.SatisfiesApartmentAxioms P.centralizer`. Only its AS 4
field is used here. Neither construction asserts the existence of the data.

## Provenance and implemented proof

These equivalences are derived internal constructions on the published
subgroups. They reuse `ChamberFiltration.rootFixer_eq_filtration_of_isFacet`,
which proves root-filtration constancy from AS 4. That result formalizes the
constancy direction of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Lemma 6.3.20, printed p. 222 / PDF p. 253. The source is registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

For every actual relative root, its facet fixer equals its filtration at
the chosen point. The singleton root fixer is the same filtration. Applying
congruence to the supremum over the relative roots gives
`sharpFixer_eq_singleton_of_isFacet`. Intersecting this identity with the
unchanged normalizer and centralizer gives the two corresponding sharp
intersection identities.

The sharp constancy also gives the point-independence assertion of KP
Lemma 7.4.4(1), printed p. 256 / PDF p. 287; the module does not claim its
more general closure-of-subsets assertion.

The full parahoric is the supremum of the actual mapped `centralizerZero`
and the sharp fixer, by the published implementation of KP Definition
7.4.1(4), printed p. 255 / PDF p. 286.
Substituting the sharp equality proves
`parahoric_eq_parahoricAt_of_isFacet`, and then equality of the parahorics at
any two points of one facet. A chamber is a facet, so the actual definition
`chamberIwahori C = parahoric C` gives `chamberIwahori_eq_parahoricAt`, the
first equality of the published `ChamberIwahoriConclusion`. This is the
point independence used with the Iwahori definition in KP Definition
7.4.5(2), printed p. 256 / PDF p. 287.

`MulEquiv.subgroupCongr` converts the sharp and full subgroup identities
into the two announced multiplicative equivalences. The coercion lemmas
are reflexive equalities because these maps retain the rational point.

The registered 1 November 2024 corrections,
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF p. 33, add AS 5 to the Chapter 7 assumptions. The full helper retains the
published apartment-axiom bundle, including AS 5. The sharp helper derives
only constancy from the earlier AS 4 law.

The module proves no sharp normalizer-centralizer equality, full-centralizer
intersection computation, unipotent intersection comparison, or product
injectivity or range assertion. Those remain parts of the exact chamber
Iwahori decomposition proof task.
