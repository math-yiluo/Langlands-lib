# Normalizer and centralizer subgroup functors of a torus

This file defines the scheme-theoretic normalizer and centralizer of a subgroup
functor. Both are tested after every refinement of the test scheme. It
specializes them to the image of a torus homomorphism `i : T ⟶ G`, compares the
result at the base with the published groups `normalizerPoints i` and
`centralizerPoints i`, and defines the quotient groups `N(U)/Z(U)` of points
together with the restriction map from `relativeWeylGroup i = N(k)/Z(k)`.

## Normalizer and centralizer of a subgroup functor

For a subgroup functor `F` of a group scheme `G` over an arbitrary base `S`:

- `SubgroupFunctor.normalizer F` contains a point `g : U ⟶ G` when, for every
  morphism `a : V ⟶ U` of `S`-schemes and every `x ∈ F(V)`, both
  `(a ≫ g) * x * (a ≫ g)⁻¹` and `(a ≫ g)⁻¹ * x * (a ≫ g)` lie in `F(V)`.
- `SubgroupFunctor.centralizer F` contains `g` when `a ≫ g` commutes with every
  `x ∈ F(V)` for every such `a`.

The membership conditions are `mem_normalizer` and `mem_centralizer`, both
`Iff.rfl`. Closure under products and inverses, and stability under
restriction, are proved inside the definitions.

These are the functors of Milne, *Algebraic Groups* (2017), source
`milne-2017-algebraic-groups`:

- Proposition 1.83, printed p.31 (PDF p.47): `N(R) = {g ∈ G(R) | g H(R') g⁻¹ = H(R')`
  for all `R`-algebras `R'`}.
- Proposition 1.92, printed p.33 (PDF p.49): `C(R) = {g ∈ N(R) | g` centralizes
  `H(R')` in `G(R')` for all `R`-algebras `R'`}.

The Lean definitions differ from the source in four ways, all of them derived.

1. The base is an arbitrary scheme, not a field.
2. The test objects are all `S`-schemes `V` with a morphism to `U`, not only
   affine ones.
3. `F` is an arbitrary subgroup functor, not necessarily represented by an
   algebraic subgroup.
4. The equality `g F(V) g⁻¹ = F(V)` is written as the two inclusions for `g` and
   `g⁻¹`.

Milne's extra requirement `g ∈ N(R)` in the centralizer is redundant here, since
`centralizer_le_normalizer` proves it. The definitions use
morphism identities after refinement. They are not the abstract normalizer or
centralizer of the group `F(S)` of base points, which differs from the
scheme-theoretic one when there are too few rational points, for instance over a
finite field (Milne 1.84 and 1.93 compare the two only under a density hypothesis).

Proved properties:

- `conj_mem_of_mem_normalizer` and `commute_of_mem_centralizer` evaluate the
  conditions at the identity refinement.
- `isNormalizedBy_normalizer`: `F` is normalized by its normalizer, in the sense of
  the published `SubgroupFunctor.IsNormalizedBy`.
- `le_normalizer`: `F ≤ normalizer F`.
- `centralizer_le_normalizer`: `centralizer F ≤ normalizer F`.
- `centralizer_isNormalizedBy_normalizer`: the centralizer is normalized by the
  normalizer.
- `normal_centralizer_subgroupOf`: for each test scheme `U`, `Z(U)` is a normal
  subgroup of `N(U)`.

`SubgroupFunctor.HasClosedRepresentative F` says that some homomorphism
`j : H ⟶ G` is a closed subgroup (published `IsClosedSubgroup`, a closed
immersion) and represents `F` (published `IsRepresentedBy`: `j` is a
monomorphism and `range j = F`). This is the representability asserted in Milne
1.83 and 1.92 for algebraic subgroups over a field. The predicate is a
definition only, and no representability theorem is proved here.

## The normalizer of a torus

For a commutative group scheme `T` and a homomorphism `i : T.toGrp ⟶ G` over any
base, `torusNormalizer i` is the normalizer of `SubgroupFunctor.range i`, the
points of `G` that factor through `i`. `mem_torusNormalizer` unfolds this: after
every refinement `a : V ⟶ U`, conjugation by `a ≫ g` and by its inverse sends
every torus point `t ≫ i` over `V` to a torus point.

The centralizer is not redefined. `torusCentralizer_eq_centralizer_range` proves
that the published `torusCentralizer i` equals the centralizer of
`SubgroupFunctor.range i`. Consequently:

- `torusCentralizer_le_torusNormalizer` gives `Z ≤ N`.
- `torusCentralizer_isNormalizedBy_torusNormalizer` gives that `Z` is normalized
  by `N`.
- the instance `normal_torusCentralizer_subgroupOf` gives that `Z(U)` is normal in
  `N(U)` for every test scheme `U`.

For a maximal `k`-split torus `S` of a connected reductive group, these are the
groups `𝒩(S)` and `𝒵(S)` of Borel–Tits, *Groupes réductifs* (1965), source
`borel-tits-1965-groupes-reductifs`, §5.1, printed p.95 (PDF p.42). In Milne they
are `N_G(S)` and `C_G(S)` of 25.16–25.17, printed p.549 (PDF p.565). The
construction itself needs neither reductivity nor maximality nor splitting.

## Comparison with the published points at the base

Write `N = torusNormalizer i` and `Z = torusCentralizer i`, and evaluate them at
the base `Over.mk (𝟙 S)`.

- `normalizerPoints_le_torusNormalizer` proves `normalizerPoints i ≤ N(S)` with no
  hypothesis on `i`. If `i ≫ int(n) = σ ≫ i` (published `IsNormalizingPoint`),
  then the constant point of `n` conjugates `t ≫ i` to `(t ≫ σ) ≫ i`. Its inverse
  uses `σ⁻¹`, via `IsNormalizingPoint.conj_comp` and the published
  `IsNormalizingPoint.inv`. `comp_eq_constantPoint` identifies a restriction of a
  base point with its constant point.
- `torusNormalizer_le_normalizerPoints` proves the converse when the underlying
  morphism `i.hom.hom.left` is a monomorphism. If `n ∈ N(S)`, then
  `SubgroupFunctor.range (i ≫ int(n)) = SubgroupFunctor.range i`, so both `i` and
  `i ≫ int(n)` represent `range i`. The published
  `SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy` then gives a group
  isomorphism `e : T ≅ T` with `e ≫ i = i ≫ int(n)`. This is
  `IsNormalizingPoint i n σ` for the corresponding automorphism `σ` of the
  commutative group scheme.
- `torusNormalizer_carrier_base` proves `N(S) = normalizerPoints i` for
  monomorphic `i`.
- `centralizerPoints_le_torusCentralizer` restates the published equality
  `torusCentralizer_carrier_base` as an inclusion.

The monomorphism hypothesis is exactly what the published `weylAction` uses. It
holds for a maximal split torus, through the published `IsSplitSubtorus.mono`.

## Quotients of points and restriction

`pointWeylGroup i U` is the quotient group `N(U) ⧸ Z(U)` of the points over the
test scheme `U`, made a group by `normal_torusCentralizer_subgroupOf`. It is a
quotient of groups of points, not the group of `U`-points of a quotient scheme or
sheaf `N/Z`. No comparison between the two is asserted in this file. Milne
25.16(c) and 25.17, printed p.549 (PDF p.565), describe the quotient
group scheme `N_G(S)/C_G(S)`, which is finite and constant, and state that every
coset of `C_G(S)` in `N_G(S)` has a representative in `N_G(S)(k)`. Borel–Tits 5.3,
printed p.96 (PDF p.43), states that every connected component of `𝒩(S)` meets
`G_k`.

`normalizerPointsRestrict i U` is the group homomorphism
`normalizerPoints i →* N(U)` sending `n` to its constant point over `U` (its
restriction along `U → S`). Its value is `coe_normalizerPointsRestrict`, which
holds by `rfl`. `normalizerPointsRestrict_mem_torusCentralizer` shows that
restriction sends centralizer points to `Z(U)`.

Over a field, with `T` and `G` over `Spec k`,

`relativeWeylGroupRestrict i U : relativeWeylGroup i →* pointWeylGroup i U`

is the induced map `N(k)/Z(k) → N(U)/Z(U)` on quotients. `relativeWeylGroupRestrict_mk`
gives its value on a coset. The published `relativeWeylGroup i` is defined only
over `Spec k`, which is why this map lives in a field section. No injectivity or
surjectivity is claimed in this file.

## Provenance

The normalizer and centralizer functors follow Milne 1.83 and 1.92. The
following are derived formulations for the published `Grp(Over S)`
architecture:

- the arbitrary base, the arbitrary test schemes and the arbitrary subgroup
  functor;
- the torus specialization;
- the base comparison;
- the quotient of points and the restriction map.

They supply the objects that the separate statement targets for closed
representatives and for the comparison of `N(k)/Z(k)` with `N(K)/Z(K)` refer to.
