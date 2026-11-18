# Inducing actual special-atlas maps through coefficients and reduction

This internal construction retains the exact supplied refined comparison under
coefficient extension, scalar-structure transport, and quotient reduction.
The inducing atlas map is extended or reduced by the existing actual formal
map construction. The complete integral formal test criterion follows from
`Comparison.InducedBy.baseChange`; scalar transport is equality elimination.

The original `SpecialAtlas.baseIdComparison` satisfies the criterion for its
actual `baseIdIso`, by its definition as the restriction to a reflexive cover.
`inducedReductionComparison` pairs the specified quotient-reduced comparison
with the proved inducing criterion for the reduced actual atlas isomorphism.

The local field and central finite-dimensional division algebra, the embedded
field and coefficient rings retain their existing assumptions and universes.
Nilp reduction allows universes {v,w}, arbitrary principal covers, and maps
merging generators. No framed comparison, quotient functor law or
representability statement is asserted here.
