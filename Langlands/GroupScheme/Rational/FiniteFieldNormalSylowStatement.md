# Normal Sylow subgroups in the defining characteristic

`Langlands.GroupScheme.FiniteFieldNormalSylowTorusStatement` is a proposition
target at arbitrary universe `u`. It isolates the finite reductive-group
input in the last paragraph of the proof of Kaletha–Prasad Proposition
13.5.2. This module states the input and supplies no proof.

For every finite field `k` and connected reductive `k`-group `G`, let
`p = ringChar k`. If a subgroup `H` of the actual group `rationalPoints G`
is a `p`-group, is maximal among `p`-subgroups, and is normal in the whole
rational-point group, then `IsTorus G`.

The `IsPGroup p H` predicate means that every element of `H` is killed by
some power of `p`. The rational points here form a finite group: connected
reductivity supplies a smooth affine group over the finite field, hence an
affine group of finite type. Thus the explicit maximality condition is
exactly the Sylow condition in the defining characteristic. Normality is
normality of `H` in `G(k)`. No normal subgroup scheme or geometric density
of the finite set `G(k)` is assumed. The conclusion concerns the actual
algebraic group over `k`, including nonsplit tori.

## Provenance and intended use

This is a derived prerequisite. In the normalizer argument on printed
p.477 / PDF p.508, KP obtain the rational points of the unipotent radical
of a Borel in a finite reductive quotient. Those points are also normal in
the whole quotient point group, and KP conclude that the reductive quotient
is a torus. The separate Sylow/Borel classification identifies these radical
point subgroups with the maximal `p`-subgroups used here.

The formulation isolates the finite-group assertion from buildings,
topology, and chosen radical representatives. Its scope includes every
connected reductive group over a finite field, since such groups are
quasi-split; the Library proves this in `finiteFieldQuasiSplit`. One proof
route is to show that normal `p`-subgroups lie in two opposite Borel
radicals whose point groups have trivial intersection. A normal Sylow
subgroup is then trivial. Nontrivial relative root groups would contribute
nontrivial `p`-subgroups over a finite field, so the reductive group must be
a torus. This is a proposed proof route, not an implemented proof.

The statement remains to be proved. Applying it to KP also requires the
actual reductive-quotient map, the Sylow and normality hypotheses for its
image, and the facet criterion that a torus quotient corresponds to a
chamber. None of those geometric or local-field conclusions is asserted
here.

Source: Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), proof of
Proposition 13.5.2, printed p.477 / PDF p.508, final normalizer paragraph.
Registered source `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The 1 November 2024 correction to Proposition 13.5.2(1) concerns the local
ambient group and does not change this finite-field input.
