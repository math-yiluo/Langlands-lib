# L-polynomials of grouped square-integrable blocks

Author: Worker 1748.

This internal reduction transports the conditional common-real-twist product
formula through actual representation equivalences. Positive total ranks are
written as successors to apply `TemperedLFactorStatement.commonRealTwists`.
The normalized determinant-twist equivalence, followed by the twist of each
supplied representation equivalence, transports the induced-pair polynomial.
No additional analytic conclusion is assumed or proved.

`isPadicRankLPolynomial_cast_iff` removes the two explicit rank transports.
`isPadicRankLPolynomial_cast_normalized_twist_iff` cancels the two negative
twists in the factor relation after identifying the common group exponents
with the block exponents and eliminating the two rank equalities.

`groupedPolynomial` pulls the polynomial family on the two total-fiber types
back to the original indices. Its evaluation lemma uses the inverse identities
of those equivalences. `prod_groupedPolynomial` commutes the middle products,
then uses the product formula for a sigma type and invariance of a finite
product under an equivalence.

All content is derived internally from the imported Library results and the
preceding common-twist adapter. The tempered analytic product formula remains
an explicit premise, and this module does not prove JPSS Theorem (9.5).
