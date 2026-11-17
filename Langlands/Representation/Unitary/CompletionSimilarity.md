# Similarities between positive-form completions

This internal helper extends an algebraic complex-linear equivalence between two
carriers with independently supplied invariant positive forms. Its premise says
that the target inner product on the images equals a strictly positive real scalar
times the source inner product. The carriers need no previously chosen topology.

The diagonal identity gives the exact norm ratio `sqrt a` under the canonical
Hilbert embeddings. Applying this identity to the inverse gives the reciprocal
ratio. Mathlib's `LinearEquiv.extend` uses these two bounds and the two dense
embeddings to construct `hilbertEquivalenceOfInner`. The module proves its values
and its inverse's values on the original carriers. Density proves uniqueness,
the inner-product ratio on the whole completions, and covariance for operators
whose continuous extensions and algebraic covariance are supplied.

The provenance is internal composition of `InvariantPositiveForm`'s published
Hilbert completion with Mathlib's bounded-equivalence extension theorem. No
irreducibility or automatic form comparison is asserted here. The covariance
lemma supplies no continuous extension of an unbounded operator; those
extensions are explicit premises.
