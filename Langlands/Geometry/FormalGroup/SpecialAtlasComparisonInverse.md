# Inverting actual special-atlas comparisons through quotient reduction

This internal module proves that scalar-structure transport,
coefficient extension along a supplied algebra map, and the actual
principal-quotient reduction preserve inversion of a specified
special-atlas comparison.

The parameters are those of the existing special-atlas and quotient
constructions: a nonarchimedean local field, a finite-dimensional
central division algebra, the supplied embedded subfield, and the
commutative coefficient algebras. The quotient-reduction result uses
an actual `Nilp` object. Covers need not be finite or equal before
refinement. This module imposes no new height or moduli hypotheses.

Scalar-structure transport is handled by eliminating equality of the
two algebra structures. Supplied-target extension then combines that
transport identity with the actual inverse/base-change identity of
`AtlasOrderComparisonInverse`. Quotient reduction specializes the
supplied map to `Nilp.quotientO`; thus its inverse comparison uses
precisely the original reduced refinements with their roles reversed.

The provenance is internal from the existing actual formal comparison
and quotient extension definitions. These are identities of specified
formal comparison data, stronger than existence of an inverse
equivalence on point functors. Framed-square compatibility and framed
isomorphism classes are separate constructions.
