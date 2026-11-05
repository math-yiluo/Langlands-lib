# Singleton sharp-fixer boundedness

For actual `B : ValuationBuildingData G` over a nonarchimedean local field of
either characteristic and at arbitrary universe `u`,
`SharpFixerBoundednessStatement` is the proposition that
`B.apartment.SatisfiesApartmentAxioms B.centralizer` implies algebraic boundedness
of every actual subgroup `B.sharpFixer {x}` in `G(F)`. The premise is exactly the
corrected apartment premise used in the centralizer-parahoric target.
This proposition is stated here and remains a proof obligation.

This is the singleton sharp-subgroup consequence needed from Kaletha–Prasad,
*Bruhat–Tits theory: a new approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
Corollary 7.3.14, printed p.251 / PDF p.282, with the generated subgroup
of Definition 7.4.1(2), printed p.255 / PDF p.286, at a singleton.
It does not restate the full corollary for all filtration-depth functions.
The corrections of November 1, 2024,
`kaletha-prasad-2024-corrections`,
SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF p.33, add AS 5 to the Chapter 7 premises; this is retained in
`SatisfiesApartmentAxioms`.

The implemented supporting theorem
`comap_sharpFixer_le_centralizerNormKernel_of_isAlgebraicallyBounded` proves
that boundedness of this sharp subgroup puts its pullback along the actual
closed centralizer inclusion `B.centralizer.j` in
`rationalCommonNormKernel B.centralizer.Z`, namely the actual `Z(F)^1`.
Smoothness of `G` supplies finite type. The centralizer closed immersion
supplies its affineness and finite type. The derived
`BoundedSubgroupNormKernel` adapter then pulls compact closure back along this
closed immersion and applies the centralizer's own rational norm characters.
The final helper applies this adapter to a proof of the named boundedness
statement and to the apartment premise.

These adapters are derived formal consequences of existing point-topology
lemmas. They do not prove sharp-fixer boundedness, put the sharp fixer in
`Z(F)^0`, or prove KP Lemma 7.4.3. In particular, no conclusion is drawn by
restricting ambient rational characters alone, and no equality of `Z(F)^1`
with `Z(F)^0` is assumed.
