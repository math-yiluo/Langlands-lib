# Ascending character quotients for real Whittaker coefficients

`RealPrincipalSeriesQuotientStatement` gives a character principal series
that surjects onto the compact-finite real standard module of any
inducing list of the prescribed rank. It also gives inclusion of the
original uniform Whittaker coefficient space in the uniform space of
that character list.

For each induction block of nonzero weight, take its two position
characters in ascending exponent order, with the same individual
parities as in the position expansion. The published ascending tail
operator gives a surjective compact and Lie intertwiner onto that
block in arbitrary surrounding lists. The parity check uses the
absolute block weight. At weight zero the prescribed two position
characters give equality of standard modules by the weight-zero
expansion. Character blocks are kept. Induction on the list composes
these surjections.

`compactlySplitStandardQuotient_ascendingExpand` supplies a compact-equivariant
section with a uniform bound on compact values. By `compactDifferenceBound_of_compactBound`,
the section satisfies the same bound at each compact difference order.

`isRealWhittakerIntertwiner_pullback` proves that precomposition with
a standard-module intertwiner preserves the exact coefficient map.
Each new coefficient is an original coefficient, so it satisfies the
character identity, smoothness and the height bound. The compact and
Lie actions transport through the intertwiner. For a uniform map,
the same precomposition also preserves the common height exponent.
Surjectivity gives every original coefficient as a coefficient in
the ascending character model.

`realAscendingWhittakerModels_eq` proves equality of the two exact
coefficient spaces for every \(r\geq 0\), every real block list of
total rank \(r+1\), and every nonzero real additive scale \(a\).
Both spaces use the same scale \(a\). The kernel of a single
nonzero-weight tail is polynomial along its lower root by
`ascendingTailKernel_polynomial`. Exact Whittaker vanishing on that
kernel and surjectivity descend every coefficient of the ascending
pair to a coefficient of the original block. The character and
weight-zero cases are identities of standard modules. Repeating this
step over the list gives descent from the full ascending expansion.

The ascending list is a permutation of the position expansion used
in the local gamma factor calculation. The quotient and kernel
vanishing supply the exact model comparison for the real
Rankin–Selberg reduction to character lists. The corresponding
principal-series passage in Jacquet's *Archimedean Rankin–Selberg
Integrals* (2009), §11, embeds the smooth induced model in a character
principal series and restricts its Whittaker form, using Lemma 2.4
for nonvanishing. [Jacquet, Proposition 11.1 and the preceding reduction, author-posted p. 82](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
