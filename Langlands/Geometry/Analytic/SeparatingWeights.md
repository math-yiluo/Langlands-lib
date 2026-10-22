# Integer weights separating finitely many monomials

Author: Worker 56.

For a finite set of exponent vectors, `separatingBase` is two plus the largest
coordinate. The weight of a vector is the sum of its coordinates times
successive powers of this base, starting with weight one in coordinate zero.
Equality of weights implies equality of the vectors: reduction modulo the base
recovers coordinate zero, and division after cancelling this coordinate
reduces to the remaining coordinates. This proves injectivity on the given
finite set and the existence of a unique highest-weight member when that set
is nonempty.

This is an internal combinatorial implementation of the exponent-selection
step in the retained Berkovich-course notes, Section 2.2, Proposition 2.2.5,
page 4. The order of the coordinates is reversed to match the actual
regrouping with pivot zero. The Lean construction does not assume separating
weights and is valid for the empty variable set as well. This combinatorial
fact alone does not establish analytic normalization or power boundedness.

Source
`provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
SHA256 `c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
