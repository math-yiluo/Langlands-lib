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

`isRealWhittakerIntertwiner_pullback` proves that precomposition with
a standard-module intertwiner preserves the exact coefficient map.
Each new coefficient is an original coefficient, so it satisfies the
character identity, smoothness and the height bound. The compact and
Lie actions transport through the intertwiner. For a uniform map,
the same precomposition also preserves the common height exponent.
Surjectivity gives every original coefficient as a coefficient in
the ascending character model.

The ascending list is a permutation of the position expansion,
which is the presentation used in the local gamma factor calculation.
This internal quotient argument supplies the model comparison for the
reduction of both real Rankin–Selberg equations to character lists.
