# Smooth models and right limits of the minimal congruent torus filtration

`minimalCongruentModel` applies `minimalCongruentModelFromDilatation` to
`InducedTorusShallow.standardModel`, `IntegralModel.dilatation` and
`IntegralModel.positiveCongruenceModel`. It returns a smooth affine
model over `fixedFieldIntegers F` with geometrically connected fibres
and integral points equal to `minimalCongruentPoints` in the generic
torus over `inertiaFixedField F`. Affineness of the generic group
follows from `IsTorus.isConnectedReductive_of_fieldSplitting`.
The connected shallow centre is geometrically connected over the
algebraically closed residue field, and the generic torus is
geometrically connected over the fraction field.
The geometric assertions for both scheme operations follow from
`IntegralModel.dilatationStructure` in
`Langlands.GroupScheme.Dilatation.StructureProof`.

`minimalCongruentRightLimit` applies the right-limit construction to the
first congruence model of the connected Néron model. The point image of
that model is the first congruence subgroup of the connected Néron
model. The addition identity identifies its level `n` subgroup with
level `n + 1` in the original model. The resulting subgroup has carrier
the union of the subgroups at depths strictly greater than `r`.

The construction follows Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
See Lemma A.5.10, Definition A.5.12 and Lemma A.5.13 (printed pp. 635–637 /
PDF pp. 666–668), Proposition B.3.6(1) (printed pp. 658–659 /
PDF pp. 689–690), Definition B.5.2 (printed p. 667 / PDF p. 698),
and Definition B.10.8 and Lemma B.10.9 (printed p. 690 / PDF p. 721).
The correction to Definition B.10.8 is in
`kaletha-prasad-2024-corrections`, version of 1 November 2024, PDF p. 50,
SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
