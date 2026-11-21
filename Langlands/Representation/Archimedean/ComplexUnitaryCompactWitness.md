# Compact test vectors for the complex signature calculation

On the unitary group all Gram determinants of the trailing rows are 1, so the compact restriction of the principal series vector `nzFunction` depends only on the angular weights. A two-row unitary block of determinant 1 preserves each trailing minor that includes both rows or neither. The proof factors the compressed matrix into the included block and an identity block. The only remaining cutoff has weight zero when the two angular weights agree.

The tests use this compact restriction, either alone or multiplied by the difference of the squared absolute values of two entries in one column. The difference is a polynomial in entries and their conjugates, invariant under the diagonal compact torus. Restricting the finite-dimensional space of right translates to the compact group preserves finite dimensionality. The published compact extension theorem then gives the vectors in the principal series.

These choices implement the compact test vectors for a direct signature comparison of the adjacent intertwining integrals, following the signature reflection in Vogan, *The unitary dual of GL(n) over an archimedean field* (1986), Proposition 10.5, p. 476 and Theorem 11.5(f)–(h), p. 479.
