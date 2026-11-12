# Closed normalizers of smooth connected subgroups over an arbitrary base

This helper module of `Langlands.GroupScheme.smoothConnectedNormalizer`
globalizes the affine case `exists_normalizer_affine` to an arbitrary base
scheme `S`.

## Main result

`exists_normalizer`: for group schemes `G` and `H` over any `S : Scheme.{u}`,
with `G` smooth and affine over `S`, and a closed subgroup `i : H ⟶ G` with `H`
smooth and geometrically connected over `S`, there are a group scheme `N` and a
closed immersion `j : N ⟶ G`, locally of finite presentation, representing the
all-test normalizer of `SubgroupFunctor.range i`. The hypotheses and
conclusion are exactly those of `SmoothConnectedNormalizerStatement`.

## Auxiliary results

- `mem_of_comp_left` and `mem_iff_schemePt`: membership of a point
  `T ⟶ G.X` in a subgroup functor depends only on its underlying morphism of
  schemes. `schemePt G z` regards `z : Z ⟶ G.X.left` as a point over
  `Z → S`.
- `NormalizerPred i`: the normalizer of `range i`, as a condition on morphisms
  of schemes into `G.X.left`. It is stable under precomposition
  (`normalizerPred_comp`).
- `mem_normalizer_of_openCover`: when `i` is a monomorphism, membership in the
  normalizer is local on the test scheme. Each normalizer test over `V` is
  checked on the pulled-back cover of `V`, using the Library's
  `mem_range_iff_openCover` for membership in the range.
  `normalizerPred_of_local` restates this pointwise.
- `isChart_baseChange`: for `b : S' ⟶ S`, let `j` represent the normalizer of
  the range of the base change of `i`. Then `j` is a chart of `NormalizerPred i`
  over `pullback.fst G.X.hom b`: a morphism `z` into the pullback factors
  through `j` exactly when `z ≫ pullback.fst G.X.hom b` satisfies
  `NormalizerPred i`. This is used for open immersions `b`.
  The Library results `range_baseChangeHom`, `normalizer_baseChange` and
  `mem_baseChange` identify the normalizer of the base-changed range with the
  base change of the normalizer.
- `exists_iso_pullback_chart`: if a closed subscheme `c₀` represents a
  condition and `c` is a chart of the same condition over `v`, then the
  pullback of `c₀` along `v` is isomorphic to the source of `c`, compatibly
  with the maps to `v`'s source.

## Proof of `exists_normalizer`

Let `𝒜` be the affine open cover of `S`, with members `Spec (𝒜.X k) → S`. For
each `k`, base change of `G`, `H` and `i` keeps all hypotheses: smoothness,
affineness and geometric connectedness are stable under base change, and
closed subgroups base change to closed subgroups (`IsClosedSubgroup.baseChange`).
The affine case gives `N k` and `j k : N k ⟶ G_k` over `Spec (𝒜.X k)`, closed
and locally of finite presentation, representing the normalizer of the
base-changed range.

The preimages `pullback.fst G.X.hom (𝒜.f k)` form an open cover of `G.X.left`.
By `isChart_baseChange`, the closed immersion underlying `j k` is a chart of
`NormalizerPred i` over the `k`-th member. The condition is stable under
precomposition and local on the source. The Library's closed-subscheme
gluing theorem `Scheme.ClosedSubschemeGluing.exists_isClosedImmersion` gives a
closed immersion `c₀ : L₀ ⟶ G.X.left`. A morphism `z` satisfies the normalizer
condition exactly when it factors through `c₀`.

`c₀` is locally of finite presentation. This property is local on the target,
and `exists_iso_pullback_chart` identifies the pullback of `c₀` to the `k`-th
member of the cover with `j k` up to isomorphism. The term
`HasRingHomProperty.instIsZariskiLocalAtTarget` supplies target locality
explicitly.

Finally, `c₀` with the structure morphism `L₀ ⟶ G.X.left ⟶ S` is a
monomorphism `i₀` over `S`. Its points are exactly the normalizer's points.
The Library's `representingHom` and `isRepresentedBy_representingHom` give a
group scheme and a homomorphism to `G` with underlying morphism `c₀`
(`representingHom_hom`) that represents the normalizer.

## Provenance

The globalization is the Zariski-local nature of Brian Conrad,
*Reductive group schemes* (2014), Proposition 2.1.6 (source
`conrad-2014-reductive-group-schemes`), whose assertion is local on the base.
The route through the Library's closed-subscheme gluing and representability
transfer is internal to this proof.
