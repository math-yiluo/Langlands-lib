# Ordered special-segment quotient coverage

Author: Worker 195.

`Langlands.Classification.OrderedMultisegmentQuotientExhaustion` is an internal
proof-decomposition target for the published `MultisegmentHeadExhaustion`
statement. It is a proposition-valued definition; this file supplies no
exhaustion proof.

Fix a prime `p`, a finite p-adic extension `F : PadicField p`, and compatible
topological data `T`. For every natural number `n` and every irreducible smooth
complex representation `π` of `GL_n(F)`, the statement asks for an actual
`T.SegmentProductDatum n` satisfying `d.IsLanglandsQuotient π`. There is no
admissibility premise. The field and representation universe parameters `uF`
and `uV` are independent; segment carriers, blocks, products and the input
representation use `Type (max uF uV)`.

The imported relation expands to three requirements:

- The segments have no earlier segment preceding a later one.
- Each actual block is a special segment head, with the strong individual
  segment-head relation from `Segments`.
- An actual surjective intertwiner maps the normalized upper-parabolic
  product to the given irreducible representation `π`.

The datum itself includes the equality between its segment-degree sum and `n`.
Full-product kernel uniqueness is absent. In particular, the proposition does
not assume that the datum already has a strong head. It also does not replace
the given `π` by an isomorphic representative.

## Internal provenance and intended use

The proposition is obtained from the published `MultisegmentHeadExhaustion`
in `MultisegmentClassificationStatement` by retaining its actual datum witness
and forgetting the full-product kernel-uniqueness clause. The existing theorem
`SegmentProductDatum.IsLanglandsHead.isLanglandsQuotient` performs that
forgetful step. This is a weakening of that published specification, not a
claim that a separately sourced or already proved classification theorem is
available.

Conversely, this coverage target is intended to be combined with the separately
published `OrderedMultisegmentHeadExistence` statement. Once both have proofs,
choose a strong head of the product supplied by coverage. Its universal kernel
equality applies to the coverage surjection and to any other irreducible
quotient map. Transitivity then supplies the strong-head relation for the
given `π`. The multiset of the datum's segments has degree `n` by its
`degree_sum` field and the finite-list sum identity. Neither of those
classification inputs is proved by this statement module.

All natural ranks, including zero, are retained from the parent target.
Positive segment degrees force a rank-zero witness to have no segments.
Producing its actual quotient map remains part of the future coverage proof;
no rank-zero theorem or witness is assumed here.
