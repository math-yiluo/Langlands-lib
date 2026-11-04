# Constancy of actual root fixers and parahorics on facets

This file implements the facet-constancy comparison needed for compact
openness of the actual chamber Iwahori. It proves no compactness or openness
assertion. Its theorem `ParahoricBuildingData.facetFixerConstancy` proves
the separate `FacetFixerConstancyStatement`, reusing
`parahoric_eq_parahoricAt_of_isFacet` from `ChamberParahoricConstancy`.
That imported module also supplies `chamberIwahori_eq_parahoricAt`, the
specialization to the existing `chamberIwahori`. The shared declarations
retain the same hypotheses and conclusions.

The source assertion is Kaletha–Prasad, *Bruhat–Tits theory: a new approach*
(2023), Lemma 7.4.4(1), printed p. 256 / PDF p. 287, using Definition
7.4.1 at PDF p. 286. The registered source is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The registered corrections of 1 November 2024,
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
were read at PDF pp. 33–35. The correction to Lemma 7.4.4 concerns
part (2); this draft implements the facet assertion in part (1).

The proof works on the existing actual root groups, valuations and apartment.
A finite valuation of an actual root-group element supplies an extended
affine root: the element belongs to its root group but not the strictly deeper
group. The affine root's value at any apartment point equals the valuation
of that same element there. Thus zero-depth membership depends only on the
signs of extended affine roots. AS 4 transports the facet relation for
the affine roots to the extended affine roots, because a positive multiple
has the same sign.

For a nonempty subset of one facet, all zero-depth root groups agree at its
points. Their intersections, their generated sharp subgroup and the join
with the image of the actual central subgroup `Z(F)^0` therefore agree with
the corresponding groups at any point of that subset. The full-parahoric
conclusion retains that central factor exactly.

The proof uses no topology comparison or integral model, and covers the
empty relative-root system without an additional argument. Its local-field
parameters are those of the published actual parahoric API; no characteristic
restriction is introduced.
