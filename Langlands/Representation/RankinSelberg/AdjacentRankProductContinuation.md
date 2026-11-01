# Continuation of actual adjacent-rank finite products

This internal prerequisite assembles the actual finite coefficient convolution
of JPSS Section 6.3, printed pp.435–436, formulas (9)–(10), on a common right
half-plane. It uses the published equal- and unequal-rank analytic proofs for
actual coefficient-image vectors of full Whittaker-type representations,
including reducible representations. Actual shifted matrix rational-value
witnesses remain explicit premises.

`scaledStandardCoefficientAsInverse` transports a vector of the coefficient
image for the scaled additive character to the inverse-character image of the
same representation. It transports the functional by equality of the two
unipotent characters and keeps both the original carrier vector and the
underlying function. It asserts no equivalence with the original carrier.

`corankOneCoefficient_convergesOnRight` specializes the unequal-rank analytic
proof to the zero-row block with complementary size zero. The zero-row Dirac
measure reduction turns its genuine integrability statement into convergence
of the actual corank-one quotient integral. The supplied quotient measure and
additive Haar measure are unchanged.

`corankOneCoefficient_productContinuation` assumes an actual finite coefficient
convolution and its pointwise determinant support bounds. Equal-rank analytics
provide convergence and rational continuation for each equal-rank factor.
Unequal-rank analytics provide corank-one convergence. The finite-family bound
lemma and the maximum with the corank-one bound give a common half-plane with
genuine convergence of every integrand, using the supplied shifted matrix-value
witnesses. The finite-product theorem therefore identifies the actual integrals
there. Finite sums of products of rational continuations and agreement on that
half-plane give continuation by the finite sum of rational products. Uniqueness
identifies every other continuation with that sum.

`adjacentRankModel_corankOne_productContinuation` obtains the actual finite
coefficient convolution from the published separated-model calculation. Its
ambient vector belongs to an actual full Whittaker-type coefficient image and
is supplied with a whole-function realization by the separated model integral.
The first and second representations have full Whittaker type as well; all
three specified functionals are nonzero. The coefficient-image transport above
recasts the second representation's scaled-standard coefficients for use in
the inverse-character analytic theorems.

The integer support bounds, natural number `N`, and family `B` in the actual
coefficient image are chosen before the second Whittaker vector `W'`. The
bi-smooth matrix coefficients `f` in that same image representation are chosen
before any complex parameter or matrix rational-value witnesses. For every
family `M` of actual shifted matrix rational values, the conclusion supplies
equal-rank rational values `A`, a common half-plane of genuine convergence and
the literal finite integral product identity there, rational continuation of
the corank-one integral by `∑ i, A i * M i`, and equality of every continuation
with this sum. The empty finite family is covered by the same finite-bound
lemma. The result does not assert existence of the matrix witnesses.

The field topology, absolute value, determinant order, residue cardinality and
Borel structures are the canonical ones. The quotient measure and normalized
general-linear Haar measure agree with those in the actual coefficient and
integral formulas. The square-matrix exponent is exactly `s + r/2` at group rank
`r+1`, including rank one. Representation universes remain independent. No
irreducibility or topology on any representation carrier is assumed.

This is a derived assembly of published analytic and coefficient results, not a
proof of matrix rationality, model realization, a functional equation or either
parent gamma/L target. No multiplicativity theorem is used.

The original source is Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg
Convolutions* (1983), Section 6.3, printed pp.435–436. The rank substitution is
ambient rank `t = r+2`, so the matrix factor's exponent `s+t/2−1` is `s+r/2`.
The source's formal coefficient identity is used here only through the
published actual coefficient theorem. Genuine convergence follows from
full-type analytic theorems and the retained matrix witnesses before the
integral identity is asserted. Theorem 3.1 (printed pp.404–405) and the remaining
steps of Sections 6–7 are outside this prerequisite's conclusion.
