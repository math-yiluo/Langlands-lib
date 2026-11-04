# The actual Weyl-action image in semisimple rank at most one

This internal helper concerns an arbitrary field, an affine group scheme
locally of finite type, a split torus, and a monomorphism from the torus to
the group. It assumes that every two actual adjoint roots are linearly
dependent over the integers. It does not require reductivity, maximality,
root reducedness, or a root-system realization.

For a nonzero root, integral dependence gives a relation whose coefficient
of the other root is nonzero. Injectivity of rationalization for a split
torus proves that this coefficient remains nonzero over the rationals.
Division then puts the other root in the rational line of the first.
`IsSplitTorus.relativeRootSpan_eq_span_singleton_of_rankOne` identifies
the whole actual rational root span with that line.
`IsSplitTorus.finrank_relativeRootSpan_le_one_of_rankOne` gives the
dimension bound and also handles the empty root set.

The published `IsSplitTorus.finite_range_relativeWeylAction` gives finite
image of the actual quotient action, without faithfulness. Consequently
each image element has finite order. On a one-dimensional rational vector
space, a linear automorphism is a scalar. A finite-order rational scalar is
one or minus one, as follows by considering its sign and a positive power
equal to one. On the zero-dimensional space every automorphism is the
identity. Thus `IsSplitTorus.relativeWeylAction_eq_one_or_neg_of_rankOne`
gives a single global sign on the whole root span.

`IsSplitTorus.rankOneRelativeWeylSignEmbedding` embeds the existing image
subgroup of `relativeWeylAction` in `Bool`: true denotes the identity and
false denotes negation. Its injectivity follows from the sign dichotomy.
The associated cardinality theorem bounds that image by two. If the root
span is zero, only true occurs.

The provenance is internal: these are derived consequences of actual root
definitions, the published rationalization injection, finite actual
root-action image, and elementary linear algebra and finite-order
arguments. No source claim about root reducedness or geometric
faithfulness is made. This module does not bound the cardinality of the
acting quotient without faithfulness and does not prove
`RankOnePositiveRootUniquenessStatement`.
