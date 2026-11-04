# Constancy of the actual full parahoric on a facet

`ParahoricBuildingData.FacetFixerConstancyStatement` states the facet part
of Kaletha–Prasad Lemma 7.4.4(1): for an actual facet `Fa` and every
`x ∈ Fa`, the actual full parahoric `P.parahoric Fa` equals
`P.parahoricAt x`. This file states the comparison; its proof is a
separate contribution.

The registered source is Kaletha–Prasad, *Bruhat–Tits theory: a new
approach* (2023), Lemma 7.4.4(1), printed p. 256 / PDF p. 287, with
Definition 7.4.1 on printed p. 255 / PDF p. 286, source ID
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The mandatory 1 November 2024 corrections, source ID
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp. 33–35, add AS 5 to the Chapter 7 hypotheses and correct the
singleton notation in Definition 7.4.1 and the function subscript in the
proof of Lemma 7.4.4. The point parahoric here uses the singleton `{x}`.

The parameters are exactly the existing actual
`ParahoricBuildingData G`, over a nonarchimedean local field in an
arbitrary universe. The explicit apartment hypothesis is
`P.apartment.SatisfiesApartmentAxioms P.centralizer`, including its
corrected AS 5 condition. The full parahoric retains the image of
`P.centralizerZero`; no substitution of the sharp subgroup is made.
The assertion covers both characteristics and an empty relative-root
system. It requires no topology, compactness or openness premise.

Every chamber in the existing API is a nonempty facet, so this
comparison applies to `P.chamberIwahori C` at any point `x ∈ C`.
Compactness and openness of that subgroup remain separate obligations.
