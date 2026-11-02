# The clopen locus of distinct related tuples

This helper develops the distinct-tuple construction in Stacks Project, Decent
Algebraic Spaces, Lemma 68.8.3 (Tag 0BBN), used again in Tag 07ST. The registered
sources are `stacks-stratification-2026-11-02` and
`stacks-noetherian-approximation-2026-11-01`. It works directly with the scheme
presentation and the related-tuple universal property, without constructing or
assuming its quotient algebraic space.

The identity section `E.unit` is an open immersion: it is a section of the
étale morphism `E.s`, whose diagonal is open. `unit_isOpenImmersion` derives
the section result using the cancellation criterion for morphism properties.
If `E.s` is separated, its diagonal is closed, and
`unit_isClosedImmersion` uses the analogous closed-immersion cancellation
criterion.

`tupleRelation n i j` is the unique relation arrow between two tuple
coordinates. `tupleRelation_t` and `tupleRelation_s` describe its endpoints.
`tupleReindex_relation` proves compatibility with all index maps by comparing
endpoints.

`tupleEqualOpen n i j` pulls back the image of the identity section along
`tupleRelation n i j`. This is an equality subscheme; it does not compare only
the ordinary point images of the coordinate maps. Its closedness follows
from that of the identity section when `E.s` is separated.
`range_subset_tupleEqualOpen_iff` proves its universal property: a family
factors through it exactly when the two coordinate morphisms agree. One
direction lifts the relation arrow through the open identity section; the
other uses uniqueness of relation arrows with prescribed endpoints.
`tupleReindex_preimage_equalOpen` records compatibility with index maps.

`tupleDistinctOpen` is the finite intersection of the complements of all
equality loci for unequal indices. `mem_tupleDistinctOpen` describes
membership. The closedness and clopen lemmas follow because all equality
loci are clopen. `tupleDistinctScheme` is its open subscheme.
Its inclusion is also a closed immersion, so it is affine whenever both
`E.U` and `E.R` are affine. `tupleDistinctProjection` restricts a tuple
coordinate to this subscheme; each such projection is étale by composition.

The separatedness assumption on `E.s` is explicit. It is available for the
affine closed presentations in the first-level task, since both schemes are
then affine. The index `n` continues to mean `n + 1` coordinates.
