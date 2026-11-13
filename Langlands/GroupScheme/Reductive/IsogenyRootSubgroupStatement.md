# Root-subgroup images and coordinates of a split group isogeny

`Langlands.GroupScheme.IsogenyRootSubgroupStatement` declares the
root-subgroup and coordinate portion of Milne Proposition 23.5. It is a
proposition declaration, with no proof supplied by this module.

Let `G` and `G'` be connected reductive groups over an arbitrary field
`k`, with specified split maximal tori `i : T → G` and `i' : T' → G'`.
Let `φ : G → G'` be an isogeny, and let `t : T → T'` satisfy
`i ≫ φ = t ≫ i'`. Specify finite reduced root data `P` and `P'` of
these inclusions on their actual character and cocharacter lattices.
For every

```
f : RootDatumIsogeny (ringExpChar k) P' P
```

whose lattice maps satisfy

```
f.weightMap χ = t ≫ χ
f.coweightMap ν = ν ≫ t,
```

the statement gives the following two conclusions for each root index
`j'` of `P'`. Write `j = f.indexEquiv j'` and `q = f.rootFactor j'`.

First, the source root subgroup `U_β` has actual fppf image
`U_(P'.root j')` under `φ` if and only if `β` has index `j`.
The Lean assertion quantifies over every source root index and uses
`SubgroupFunctor.IsFppfImage` on the intrinsic
`RelativeRoot.subgroup` functors.

Second, choose any group morphisms `x : Ga → G` and `x' : Ga → G'`
that represent the corresponding entire root-subgroup functors and
satisfy full-torus equivariance for `P.root j` and `P'.root j'`,
respectively. There is a single `c ∈ kˣ`, depending on these
parametrizations and `φ`, such that on every test scheme `Z` over `k`
and every `a ∈ Γ(Z, O_Z)`,

```
φ(x_Z(a)) = x'_Z(c_Z * a^q).
```

Here `c_Z` is the pullback of the field scalar `c` to global functions
on `Z`, explicitly

```
Z.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv (c : k)).
```

`VectorGroup.scalarPoint` supplies the additive point with coordinate
`a`. The scalar `c` is chosen before `Z` and `a`. Thus the displayed
equation is a natural scheme formula, including on nonaffine and
nonreduced tests, rather than an assertion only about `k`-points.

## Hypotheses and conventions

The ambient architecture is `Grp (Over (Spec k))`. Geometric
reductivity is the published predicate `IsConnectedReductive`.
`IsIsogeny` means finite, flat and surjective on the underlying scheme
morphism. No smoothness of the kernel, separability of `φ`, perfectness
of `k`, pinning or choice of standard coordinates on the tori is
assumed.

Each of the four lattice-finiteness instances comes from the appropriate
split-torus hypothesis. Both root indexing types are finite, and both
root data are reduced. `IsRootDatumOf` identifies their pairings with the
actual torus pairings, their roots with the adjoint roots, and their
reflections with normalizer actions.

The root-datum isogeny is in the character-pullback direction `P' → P`.
Consequently its root equation reads
`t ≫ P'.root j' = q • P.root j`, with `j = f.indexEquiv j'`.
Its factor is a positive power of the field's characteristic exponent:
one in characteristic zero and a power of the prime characteristic
otherwise. The supplied compatible `f` does not assume either image
comparison or coordinate conclusion. Reducedness and positivity
determine the root correspondence and factor from its actual weight
map, so the target applies to every such `f`.

`RelativeRoot.subgroup` is defined intrinsically by extension of the
torus-conjugation orbit through the root character to the affine line,
with identity value at zero. `IsRepresentedBy x` requires monicity and
equality with the all-test range of `x`. The parametrizations therefore
identify `Ga` with the whole root subgroup. `IsTorusEquivariant` is the
actual scalar conjugation law on every test scheme.

`IsFppfImage` requires representatives of both root functors and a
commuting induced map between them that is flat, surjective and locally
of finite presentation. This records the actual image subgroup. For
`a ↦ c a^q`, surjectivity can require an fppf refinement of the
original test. Equality with the ordinary pointwise image on every
original test would fail for Frobenius. The full scheme kernel is
retained.

## Original source and companion target

The source is J. S. Milne, *Algebraic Groups: The Theory of Group Schemes
of Finite Type over a Field* (2017), Proposition 23.5 and its proof,
printed pp.485–486, one-based PDF pp.501–502. The preceding formula
(144) fixes the full-torus equivariance convention. Formula (145)
displays the coordinate conclusion on `k`-points, while (146) and the
following argument establish it for every `k`-algebra; this gives the
scheme formula used here. The source's image root groups are expressed
by their actual fppf image, which also accommodates inseparable maps.
The registered source is `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

The complete retained official errata snapshot,
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`,
has no correction to Proposition 23.5.

The separate published `IsogenyRootDatumStatement` asserts existence
of a compatible `f`, the torus-isogeny conclusion, and centrality and
isomorphism comparisons. The present target adds the root-subgroup
image criterion and power-coordinate formula for any compatible `f`.
It does not assume a proof of that companion and does not supply one.
