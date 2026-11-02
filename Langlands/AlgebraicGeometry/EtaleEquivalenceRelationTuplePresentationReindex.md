# Actual chart comparisons for finite symmetric tuple subfamilies

This is derived infrastructure for the finite symmetric tuple scheme charts
in Stacks Project, Lemma 68.8.6 (Tag 07ST), and the construction of Lemma
68.8.3 (Tag 0BBN). The registered originals are
`stacks-noetherian-approximation-2026-11-01` and
`stacks-stratification-2026-11-02`. The finite presentation and its threshold
opens were constructed in the preceding Library modules. A tuple parameter
`n` means `n+1` entries.

The module assumes an étale equivalence relation `E`, separated source,
affine object and relation schemes, and a closed joint endpoint map. Its
finite index types may be empty, and chart lengths may repeat. These are
the hypotheses of the existing finite tuple presentation, in arbitrary
scheme universe `u`.

`tupleChartReindexObjectMap length k` and
`tupleChartReindexRelationMap length k` are the coproduct maps induced by
an index map `k`. The component equations identify their restrictions to
each object and cross-correspondence. The `t` and `s` equations retain both
endpoints. Injective index maps give open and closed immersions on both
objects and relations, by the generic finite subfamily theorem.

`tupleChartReindexChartMap` maps the selected relation scheme to the actual
`Chart.arrows` of the full presentation along its object map. Its three
equations identify both endpoints and the map to the full relation scheme.
For injective `k`, `tupleChartReindexChartIso` is the actual isomorphism from
the selected relation scheme to this induced chart relation.
`tupleChartReindexChartIso_hom` identifies its forward morphism with the
explicit chart map. All these results specialize the generic
`FiniteSchemeRelation` comparison; the selected tuple data and the
reindexed finite relation data agree by their definitions.

`tupleChartReindexObjectMap_threshold_preimage` identifies the inverse image
of each total threshold with the same threshold in the selected family.
Its proof decomposes a point of the selected object coproduct into a chart
component, applies the object component equation, and uses the established
component threshold membership formula. This formula holds for every
index map, without an injectivity assumption.

`tupleTailObjectMap` and `tupleTailRelationMap` specialize to the tail
of lengths `p` through `N` inside the full finite family. The object map
has open and closed immersion instances, and the relation map retains
both endpoints. `tupleTailChartMap` and `tupleTailChartIso` provide the
explicit induced chart map and the actual relation-scheme isomorphism,
with its forward-morphism and endpoint equations. Empty tails are allowed.

`tupleTailIndexMap N p q hpq` includes the indices of the higher tail in
the lower tail under `hpq : p ≤ q`; its injectivity follows by taking
subtype values. `tupleTailToTailObjectMap` is the resulting open immersion,
and `tupleTailToTailChartIso` identifies the higher-tail relation scheme
with the actual induced chart relation of the lower tail.

These comparisons involve both endpoints. They do not assert that a raw
tail inclusion gives a cartesian source square, that every equivalence
class meets the selected family, or that a Noetherian first level exists.
