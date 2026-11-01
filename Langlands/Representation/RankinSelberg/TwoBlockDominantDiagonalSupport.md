# Compact support of diagonal test restrictions on determinant slices

Worker 113 derives compact support on a fixed determinant slice for the norm
of a smooth Whittaker coefficient restricted from a strictly larger general
linear group through the actual diagonal inclusion. The proof uses the
Section 4.5 common compact support argument, not later analytic consequences.

The corank-one case uses `CommonLevel.corank_common_compact_support` with a
constant family. The auxiliary inverse-character function is the pointwise
reciprocal of the diagonal restriction. Thus its product with the restriction
is nonzero wherever the restriction is nonzero. The compact set supplied for
the corank integrand also contains the norm support. Its closedness contains
the closure of that support. Repeated smooth pullback through `rankInclusion 1`
proves the result for any positive rank gap. No nonzero functional is required.

The supporting constructions `diagonalWhittaker`, `reciprocalWhittaker` and
`diagonalFunctional` retain the actual diagonal inclusions and original supplied
functional. No regularity of the reciprocal and no integral identity is claimed.

This is derived infrastructure for the first-block argument of JPSS (1983),
Sections 4.9 and 4.10(2), printed pages 416–419, using the already implemented
Section 4.5 support argument. Source: `jpss-1983-rankin-selberg`, retained PDF
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
