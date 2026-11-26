# The local-domain saturation of a saturated atlas is the same atlas

This module proves that the Library's construction of the atlas of all local
full affinoid domains, `IndexedAffinoidAtlas.saturatedAtlas`, is idempotent
on the nose. Let `K : Type u` be a complete ultrametric normed field, `X` a
topological space in universe `v`, and `a : IndexedAffinoidAtlas.{u, v, w} K X`
an arbitrary atlas. Then

```text
a.saturatedAtlas.saturatedAtlas = a.saturatedAtlas
```

is an equality of atlases: the same index type, the same presented algebras,
the same chart maps and the same bounded restriction maps. No Hausdorff,
compactness, strictness or reducedness assumption is used, and the universes
`u`, `v`, `w` are independent.

## Declarations

- `IndexedAffinoidAtlas.ext_of_heq`: two atlases on the same space are equal
  when their index types are equal and their algebra, chart and restriction
  families agree up to `HEq`. The remaining fields are propositions.
- `IndexedAffinoidAtlas.saturatedAtlas_saturatedAtlas`: the idempotence
  stated above.
- `AffinoidAtlasPresentation.saturatedPresentation_saturatedPresentation`:
  for a presentation `A`, saturating `A.saturatedPresentation` again returns
  `A.saturatedPresentation`, on the same literal space.
- `SaturatedAtlasPresentation.ofSaturation_saturatedPresentation`: the
  constructed saturation `ofSaturation A.saturatedPresentation` is the same
  object of the saturated category as `ofSaturation A`.

## Proof

Write `b = a.saturatedAtlas`. Its index type is the family
`a.localDomainFamily` of ambient loci of local full domains of `a`, and the
index type of `b.saturatedAtlas` is `b.localDomainFamily`. The published
`localDomainFamily_saturatedAtlas` states that these two families of subsets
of `X` are equal, so the two index types are equal.

For a member `S` of `b.localDomainFamily`, let `i` be the same subset read as
an index of `b`. The chart of `b` at `i` has range `i` (`range_saturatedChart`),
so `S` is the original chart index `b.originalSaturatedIndex i` of the
saturation of `b`. The construction `saturatedRepresentative` chooses the
whole chart domain whenever a member is the range of an original chart; the
published `saturatedRepresentative_original` records this choice. Hence the
representative chosen for `S` is `b.originalLocalDomain i`, the whole domain
of the chart `i`. Consequently:

- the algebra of `b.saturatedAtlas` at `S` is the algebra of `b` at `i`, since
  the whole domain `Domain.whole` keeps its base algebra;
- the chart of `b.saturatedAtlas` at `S` is the ambient map of the whole
  domain, which is the chart of `b` at `i` by `originalLocalDomain_ambientMap`;
- a restriction of `b.saturatedAtlas` is the restriction of a local-domain
  inclusion between two whole chart domains, which is the original
  restriction of `b` by `originalLocalDomain_restriction`.

Each of these identifications is proved by generalizing the chosen
representative to a variable equal to the whole chart domain and substituting,
and the three families are compared by `Function.hfunext` along the equality
of index types. `ext_of_heq` then gives equality of the atlases. The
statements for presentations and for objects of the saturated category follow
by congruence; the saturation property of `SaturatedAtlasPresentation` is a
proposition.

## Provenance

This is an internal fact about the Library's choices in
`SaturatedAffinoidAtlas`, derived from the published equality of local-domain
families in `SaturatedAtlasDomainClosure` and the whole-chart lemmas in
`SaturatedAffinoidAtlas` and `AtlasSaturationComparison`. It reflects the
geometric fact that a local full affinoid domain of a local full affinoid
domain is again one; it is not a statement taken from a source.
