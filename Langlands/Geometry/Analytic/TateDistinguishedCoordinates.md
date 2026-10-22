# Distinguished coordinates for an actual nonzero Tate series

Author: Worker 56.

The proof constructs a finite set of the coefficients attaining the norm of a
nonzero series. Explicit base-power weights separate these exponents and give
one highest-weight member. The actual triangular coordinate substitution and
actual restricted-series regrouping send each selected monomial to a monic
polynomial of the corresponding weight. Their finite sum therefore has a
precisely identified leading coefficient: the original nonzero scalar
coefficient of that highest-weight monomial.

This scalar is a unit in the smaller Tate algebra. The norm-preserving
substitution bounds the polynomial coefficients by its norm. The remaining
series has strictly smaller norm, so the proved unit-perturbation lemma shows
that the entire transformed series is distinguished. Neither a distinguished
output nor a polynomial representative is assumed.

This implements the argument of the retained Berkovich-course notes, Section
2.2, Proposition 2.2.5, page 4, with coordinate zero as pivot. The independent
implementation uses an explicit inverse substitution, finite coefficient
superlevel sets, and norm attainment. The resulting distinguished coordinates
supply the finite-variable reduction used in Noether normalization.

Source
`provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
SHA256 `c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
