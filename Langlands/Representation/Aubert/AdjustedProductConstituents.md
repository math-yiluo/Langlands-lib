# Actual product constituents under adjusted Aubert duality

This internal module transports constituents of an actual normalized binary
product across the support-adjusted Aubert operator. The neighboring Speh
argument uses it to pass from a constituent of a product of two Langlands
heads to a constituent of the product of their adjusted duals. It is derived
material, not a statement from the literature. It records, at the level of
actual representations, the fact that the Aubert involution is a ring
automorphism of the Grothendieck ring that permutes irreducible classes.
This is the GL form of Aubert 1995 (`aubert-1995-duality`), Theorem 2.3,
as already formalized in the published Library declarations listed below.

The module takes no hypotheses. It uses only published Library results:

- `LanglandsHeadDuality.adjustedOperator_irreducible_eq`: the adjusted operator
  sends every actual irreducible class to an actual irreducible class;
- `LanglandsHeadDuality.coeff_gradedAdjustedOperator`: hence it transports
  graded coefficients;
- `adjustedHomogeneousMultiplicativity` with
  `gradedOperator_multiplicative_of_homogeneous`: multiplicativity of the
  graded adjusted operator;
- `binaryProductExactness` and the actual graded multiplication.

`coeff_actualProduct` identifies the coefficient of an irreducible class in
the graded product of two actual irreducible basis classes with the
composition multiplicity in the actual normalized binary product. The proof
expands the homogeneous multiplication into the finite-length class of the
product. `graded_image_of_actual` converts a rankwise equality of adjusted
classes into the matching equality of graded basis classes.

`compositionMultiplicity_eq_of_adjusted` takes irreducible representations
`A`, `B`, `C` and irreducible `AD`, `BD`, `CD` whose classes are their
adjusted images. It shows that `C` has the same composition multiplicity in
`A × B` as `CD` has in `AD × BD`. The proof applies multiplicativity to the
product of the basis classes of `A` and `B`. It then transports the
coefficient of `C` to that of `CD` and identifies both coefficients with
actual multiplicities. Any finite-length witnesses for the two products are
accepted.

`exists_adjusted_isSubquotient` is the form used downstream. Let `C` be an
irreducible subquotient of `A × B`, and let `AD`, `BD` be supplied irreducible
adjusted duals of `A`, `B`. Then some irreducible `CD` has class equal to the
adjusted image of `C`, and `CD` is a subquotient of `AD × BD`. The dual `CD`
comes from `adjustedOperator_irreducible_eq`. Positivity of a composition
multiplicity is equivalent to being a subquotient, and the previous lemma
equates the two multiplicities.

All ranks, including zero, are allowed, with independent field and carrier
universes. The operator `adjustedOperator.{uF, uV}` is definitionally equal to
`adjustedOperator.{uF, max uF uV}` on these representations, so hypotheses
stated at the carrier universe `max uF uV` can be supplied directly. The
module does not identify any Speh dual and assumes no multisegment
algorithm.
