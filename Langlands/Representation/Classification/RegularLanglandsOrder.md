# Ordering exponent-preserving matches of regular Langlands data

Author: Worker 47.

This is an internal construction for the ordered comparison required by
`Langlands.GLRegularLanglandsDataUniquenessStatement`. It uses only the published
`TemperedLanglandsDatum` and elementary order theory. It asserts no
representation-theoretic classification result and requires no new literature
claim.

Given two regular tempered data `d` and `e` of the same rank, an equivalence `a`
of their finite block-index sets, and equalities
`d.exponent i = e.exponent (a i)`, `orderIsoOfExponentEquiv` constructs an order
isomorphism whose underlying equivalence is exactly `a`. Both exponent functions
are strictly decreasing. Thus `a i ≤ a j` is equivalent to the reversed
inequality of the corresponding exponents, which is equivalent to `i ≤ j`.
The implementation applies Mathlib's `StrictAnti.le_iff_ge` twice.

`orderIsoOfExponentEquiv_toEquiv` records the definitional equality of the
underlying equivalence with the input. `exponentEquiv_unique` shows that any two
exponent-preserving equivalences agree, using injectivity of the exponent
function of `e`.

`orderedBlockMatching` carries a supplied equality of each block rank and an
actual smooth-representation isomorphism after that rank transport through the
construction. The index function does not change, so the original equalities
and isomorphisms remain the witnesses. Its conclusion has precisely the local
ordered-comparison form in the regular uniqueness statement.

The field universe and common block-carrier universe are independent. No
positive-rank hypothesis is needed by these order arguments, and the empty
index case is included. The final classification theorem may specialize the
carrier universe to `max uF uV`.

The outstanding classification proof must still obtain the rank, exponent and
block-isomorphism match from the two weak irreducible quotient witnesses.
Neither such a match nor a quotient or head existence result is proved here.
