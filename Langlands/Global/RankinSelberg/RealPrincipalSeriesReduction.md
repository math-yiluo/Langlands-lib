# The real-place functional equation from the principal-series equations

`RealPlacePrincipalSeriesReductionStatement` gives the exact real-place
functional equation from the following four premises.

- `RealUniformPrincipalSeriesInclusionStatement` puts each uniform
  Whittaker coefficient space in the corresponding expanded coefficient
  space, for the same real additive parameter.
- `RealLocalPrincipalUnequalJacquetStatement` supplies the local unequal-rank
  package for two lists of real characters.
- `RealLocalPrincipalPositiveEqualJacquetStatement` supplies the local
  equal-rank package for two lists of real characters and a Schwartz test
  function when the common rank index is positive.
- `RealPlaceContragredientPairLStatement` identifies the actual global dual
  denominator with the denominator from the blockwise inverse lists.

For a presentation given by a list of characters, the coefficient source
is the K-finite part of the position principal series. Its standard module
has no induced blocks, so the Fourier vanishing conditions in
`realStandardModule` are vacuous. The first premise concerns the resulting
functions on the group, whereas the inclusion of the underlying standard
modules concerns their source vectors. Comparing the coefficient maps
requires additional representation theory.

The two local principal-series premises use the established source
conventions, with additive parameters `a` and `-a` in the two Whittaker
spaces, epsilon parameter `-a`, positive scale `sqrt |a|`, and blockwise
inverse lists for the dual factors. The equal-rank dual integral uses the
Fourier transform with parameter `-a`. The unequal determinant sign is
`det(ds,-1)^(t+1) * det(es,-1)`. The equal determinant sign is `det(ds,-1)^r`.

The proof reuses the two integrals, their convergence and holomorphy
conditions, and the meromorphic continuation witnesses in each expanded
equation package. The primal reciprocal L-factor denominators of the
expanded and original lists are both nonzero on the codiscrete filter.
Multiplying the expanded equation by its primal denominator gives the
equation with coefficient `pairMultiplier`, times the scalar sign.
`pairMultiplier_expand` replaces this coefficient with that of the
original lists. Dividing by the original primal denominator yields the
desired equation. The reflected dual denominator occurs only through its
inverse and needs no cancellation.

Each expanded presentation is a list of real characters of the same
rank. The two applications of the principal-series premises use the
assumed coefficient inclusions at `a` and `-a`. The determinant
comparison at `-1` supplies the two original signs. The published
`realPlaceUniformLocalTheoryReduction` then uses the actual global
memberships, the dual comparison, the convention conversion, and the
rank-index-zero Tate argument. The conclusion retains the target's free
number-field universe and includes both ranks.

This internal reduction implements the factor and equation transfer in
Jacquet's principal-series reduction. The four displayed premises remain
proof obligations. [Jacquet, *Archimedean Rankin–Selberg Integrals*, §11, pp. 81–82](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
