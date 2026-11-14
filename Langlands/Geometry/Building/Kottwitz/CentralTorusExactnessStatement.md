# Right exactness of inertia coinvariants for a central torus quotient

This module states that inertia coinvariants of algebraic fundamental groups
form a right-exact sequence for a quotient of a connected reductive group by a
central torus. The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), source ID `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:

- proof of Lemma 11.5.1, printed p. 430 / PDF p. 461: the bottom row
  `π₁(Z)_I → π₁(G̃)_I → π₁(G)_I → 1` of the commutative diagram, which is
  exact, for a z-extension `1 → Z → G̃ → G → 1`;
- proof of Proposition 11.5.3, printed p. 431 / PDF p. 462: “The sequence
  `X_*(Z)_I → π₁(G̃)_I → π₁(G)_I → 0` is exact, since taking
  `I`-coinvariants is right-exact.”

The authors' corrections of 1 November 2024 have no entries for §§11.4–11.5.

## The statement

`CentralTorusInertiaExactnessStatement` quantifies over every field tower
`k → K → E` with `IsScalarTower k K E`, `E` a separable closure of `k`
(`IsSepClosure k E`) and `K/k` normal. The inertia group is the Library's
`relativeInertia k K E`, the kernel of restriction `Aut_k(E) → Aut_k(K)`. In KP,
`K` is the maximal unramified extension of a local field and this is the
inertia group; the Library's inertia targets in
`Langlands.Geometry.Building.Kottwitz.FundamentalGroup` use the general tower,
and this statement uses the same convention.

The group data are the same as in
`Langlands.GroupScheme.AlgebraicFundamentalGroup.CentralTorusFundamentalExactnessStatement`.
`Z` is a `k`-torus (`IsTorus Z.toGrp`) and `H` and `G` are connected reductive
`k`-groups. The homomorphism `i : Z → H` is a closed subgroup
(`IsClosedSubgroup i`) and central (`IsCentral i`). The homomorphism
`p : H → G` is the represented fppf quotient by the full subgroup functor of
`Z` (`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p`: flat,
surjective, locally of finite presentation, with actual scheme kernel equal to
the image of `i` on every test scheme).

For the maps `fundamentalInertiaMap` already defined in
`Langlands.Geometry.Building.Kottwitz.FundamentalGroup`, it asserts:

1. the map `π₁(H)_I → π₁(G)_I` induced by `p` is surjective;
2. its kernel equals the range of the map `π₁(Z)_I → π₁(H)_I` induced by `i`.

Here `π₁(-)_I` is `FundamentalInertia`, the actual integral coinvariants of the
actual Galois representation on the chosen fundamental-group presentation.
`π₁(Z)` uses the published proof `IsTorus.isConnectedReductive_of_fieldSplitting`
that a torus is connected reductive. The maps are the selected descents of the
actual `fundamentalGroupMap`; no descended map, exactness, surjectivity, chosen
lift or Kottwitz-square witness is a hypothesis. Unique existence and
equivariance of the descents are the separate obligations
`FundamentalInertiaMapStatement`, which this statement neither assumes nor
changes.

## Provenance and scope

KP states the row for z-extensions. This statement is a derived
generalization to an arbitrary central torus, in every characteristic. It
follows from the exact sequence `0 → π₁(Z) → π₁(H) → π₁(G) → 0` of Galois
modules (the companion group-scheme statement) and right exactness of
coinvariants, which is the argument quoted above.

Injectivity of `π₁(Z)_I → π₁(H)_I` is deliberately not asserted. KP deduces it
in the proof of Proposition 11.5.3 from torsion-freeness of `X_*(Z)_I` for an
induced torus. It can fail for other central tori. For example, take a
quadratic extension `L/k` that is not contained in `K`, so that `I` acts
through `Gal(L/k)`. Let `H = R_{L/k} G_m` and let `Z` be its norm-one torus,
with quotient `G_m` given by the norm. Then `X_*(Z)_I = ℤ/2ℤ` maps to zero in
`X_*(H)_I = ℤ`. No surjectivity on rational points of `H → G` follows from
these lattice statements, and none is asserted.

## The z-extension case

`CentralTorusInertiaExactnessStatement.zExtension` derives, from the general
statement, both conclusions for every z-extension `z : ZExtension G`
(KP §11.4). It uses the fields of `IsZExtension` and a private helper proving
that an induced torus is a torus. This is the case used in KP Lemma 11.5.1. It
is an implication from the statement, not a proof of it.
