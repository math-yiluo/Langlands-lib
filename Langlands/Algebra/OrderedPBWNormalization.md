# Normal forms for ordered Lie words

Author: Worker 1687; uses Worker 1431's ordered-word and shortlex helpers.

This internal construction instantiates `TriangularNormalization.normalize`
with the actual adjacent-inversion Lie-word reductions. Triangularity is proved
in `OrderedPBWReduction`, and local coherence is proved in `OrderedPBWCoherence`
by disjoint swaps and Jacobi. No normal-form or PBW hypothesis is supplied by a
caller: `normalForm b` is constructed for every field, every Lie algebra and
every supplied basis indexed by `Fin n`, with independent universes for the
field and Lie algebra. Zero dimension and every characteristic are retained.

`normalForm_rule` states invariance under every concrete reduction.
`normalForm_ascending` fixes the unit singleton at every nondecreasing word,
and `normalForm_supported` says that all normal forms are supported on such
words. `ker_normalForm` identifies the kernel exactly with the linear span of
all concrete rewrite differences. These follow by specializing the generic
normalizer to the proved triangularity, coherence and irreducibility results.

The relation span is preserved by `prepend i`, because prepending a generator
difference is itself a generator difference by the cons constructor. Finite
basis expansion gives preservation by `insert b x` for every `x : L`.
Combining this with `p - normalForm b p` belonging to the relation span proves
`normalForm_insert_normalForm`: an inner normal form can be removed whenever
another insertion and normalization follow it.

Finally `normalForm_insert_pair` proves the Lie commutator identity after
normalization for arbitrary inserted `x,y : L` and arbitrary word polynomial
`p`. The shorter-word commutator lemma from the coherence module applies to
each singleton, since the normalizer respects every reduction. Linearity
extends it over `p`; basis expansion extends the remaining basis argument to
all `y`. This is a proved identity, with no generator-injectivity assumption.

This unit constructs the word normalizer and identities needed for a
representation of the actual universal enveloping algebra. The representation,
ordered-monomial independence, and full span in that algebra remain the final
application; this helper alone claims no completed PBW theorem.
