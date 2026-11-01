# Growth bounds for fixed-slice convergence

This internal derived module adapts the published uniform functional growth theorem
`TwoBlockConvergence.exists_growth` to a standard-character functional on a full
Whittaker-type representation. The canonical character is nontrivial and trivial
on a sufficiently small integral level; the proof repeats the canonical valuation
comparison from the inverse-character specialization. No irreducibility or
nonzero-functional premise is used.

`exists_coefficient_growth` applies this bound to a preimage under the actual
surjective coefficient-image map and replaces the vector constant by its maximum
with zero. Its base precedes every model vector. This is a growth estimate,
not outer convergence.

`isEntryBounded_torus` shows that a diagonal uniformizer matrix and its inverse
are entry-bounded by any common bound on the positive and negative exponents.
For diagonal entries this is the nonnegative-power integrality lemma, and the
off-diagonal entries vanish. `exists_coefficient_torus_growth` combines this
with entry boundedness under multiplication. Every integral compact factor is
entry-bounded at level zero; a fixed left translate contributes a fixed power
of the growth base to the vector constant. The base still precedes the vector,
the fixed left translate, and every diagonal and compact factor.

`torusSize` is the sum of the natural absolute values of the integer diagonal
exponents. Each signed coordinate lies between its negative and positive cast.
`exists_coefficient_torusSize_growth` specializes the preceding estimate to
this size, with one base for every coefficient-image vector and left translate.

`exists_section_growth` uses the published block inverse-functional estimates
and `TwoBlockConvergence.exists_integral_growth`. The latter bounds the
untwisted tensor contractions of section values on the compact integral group.
Opposite-parabolic covariance at the opposite Levi embedding contributes the
inverse upper half modulus. The exact tensor twist identity contributes
the first block determinant norm to the power `-u` and the second to `u`;
the norms of the complex powers are the real powers displayed in Lean.
The product of the two functional growth bases is chosen before the real twist
and the section. Only the nonnegative multiplicative constant depends on them.

All assertions are internal consequences of the imported uniform functional
and compact-section growth results, with their full Whittaker-type hypotheses.
They require neither irreducibility nor nonzero supplied functionals.
This module does not assert support bounds, lattice summability, or convergence
of the lower-quotient integral.
