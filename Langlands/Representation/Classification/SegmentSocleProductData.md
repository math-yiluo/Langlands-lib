# Empty and reindexed actual segment-socle product data

This internal auxiliary module supplies empty segment-product data and elementary
transport results for actual segment socles. It also proves the zero-rank case
of multisegment socle exhaustion, without any positive-rank classification input.

`SegmentProductDatum.empty` has length zero, the empty family of segments, and
the empty family of actual blocks. Its degree is zero, its multisegment is empty,
and its precedence and segment-socle conditions hold by elimination of `Fin 0`.
`HasSegmentSocles.permute` carries each supplied socle together with its segment
under the already published reindexing operation. `permute_multisegment` retains
all occurrences, including repetitions, by the permutation theorem for
`List.ofFn`; it asserts no isomorphism of induced products.

The first algebraic lemma upgrades an irreducible embedding into an irreducible
ambient representation to a strong socle. Every irreducible embedding is nonzero
because it is injective on a nontrivial carrier. Irreducibility of the ambient
representation then makes it surjective. Thus every such image is the whole
ambient space, which proves uniqueness as a subobject.

For a trivial group, the existing scalar-line quotient lemma supplies a
surjective intertwiner from a scalar-line representation to any irreducible
representation. The line is irreducible and the map is nonzero, so this
intertwiner is also injective. Its inverse is the required embedding into the
line. The preceding image argument proves the strong socle relation.

`emptySegmentProduct_isZelevinskySocle` applies this argument to the actual
normalized empty product on `GL₀(F)`. The published
`rankZeroNormalizedProductLinearEquiv` identifies its carrier with the complex
line: this construction evaluates induction from the whole trivial group and
identifies the empty tensor product with its scalar ring. The empty datum
therefore gives `multisegmentSocleExhaustion_rankZero`, with the degree equality
and the strong socle relation exactly as in the full exhaustion statement.
Independent field and carrier universes, arbitrary primes, and the supplied
compatible topology are preserved.

The dependency audit is at the level of the implemented proof. This module
imports `OrderedMultisegmentHeadReduction` only for
`isIrreducible_of_linearEquiv_complex` and
`rankZeroNormalizedProductLinearEquiv`. Their proofs use elementary simple-module
facts, evaluation of induction from the whole group, and the empty tensor
equivalence. Neither uses any ordered head theorem or any classification
conclusion. That imported module also contains conditional head assembly lemmas
and imports classification statements, but none is used here. The other project
imports provide segment-product definitions and reindexing, and the elementary
scalar-line quotient map for a trivial group. No special-head exhaustion,
ordered special-head existence, analytic segment classification, tempered block
uniqueness, square-integrable classification or exhaustion, or regular
exhaustion conclusion is used directly or transitively by these proofs.

No positive-rank exhaustion, ordered socle existence, unlinked product
commutation, or linked embedding reduction is established by this module.
