# Division by normalized distinguished series

Author: Worker 56.

The predicate imported from `RestrictedSeriesDefinitions` refers only to the
actual coefficients: the
coefficient in degree `d` is one, every coefficient has norm at most one,
and every coefficient above `d` has norm strictly below one. It assumes no
division map, factorization or output algebra.

The polynomial truncation through degree `d` is monic of degree `d`.
The remaining tail has norm strictly below one. This last assertion uses
the fact that the coefficient supremum of a restricted series is attained;
a mere pointwise strict inequality would not suffice without that fact.
The constructed small-perturbation division theorem then gives the unique
quotient and actual polynomial remainder, with sharp norm bounds.

This is the normalized, unit-radius distinguished case of the analytic
Weierstrass division theorem in the retained Berkovich-course notes,
Section 2.2, page 3 (printed Proposition 2.1.1, later cited as 2.2.1).
The coefficient ring is a complete, nontrivial ultrametric normed
commutative ring. The separate `WeierstrassPreparation` and
`DistinguishedNormalization` modules develop preparation and leading-unit
normalization. Variable regrouping and Noether normalization are developed
in separate modules.

Source `provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
SHA256 `c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
