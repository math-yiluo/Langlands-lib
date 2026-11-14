# Division-algebra row spaces of universal split-torus weights

This internal construction applies to a split torus in the unit group of a finite-dimensional
matrix algebra over a division algebra. It uses the published universal weight idempotents of
`FiniteAlgebraWeightIdempotents`; no infinitude, characteristic, or faithfulness assumption is
needed.

For an integral exponent vector `m`, `rowWeightProjection` is right multiplication on rows
by the coefficient idempotent `weightElement i m`, and `rowWeightSpace` is its fixed subspace
over the division algebra. Orthogonality and completeness of the idempotents show that the
projections isolate the individual spaces and sum to the identity. Applying a projection
to a finite relation proves independence. These facts give an internal direct sum and
the canonical linear equivalence `rowWeightDecomposition`.

The row weight space is nonzero exactly when its exponent lies in the finite support of
the inverse-right regular representation. For the nonzero direction, at least one row of a
nonzero idempotent is nonzero and fixed by that idempotent.

The construction and proofs are derived linear algebra using the published coefficient
idempotents. They are intended as infrastructure for the maximal split-torus weight theorem
for quaternionic isometry groups.
