# Euler polynomials and unramified parameter classes

This is an internal construction and deduction from the existing local-factor
and correspondence interfaces. It makes no new literature assertion.

`LocalFactor.WeilDeligne.eulerPolynomialClass` descends the actual polynomial
`det(1 - X Φ | (ker N)^I)` to genuine pair-isomorphism classes, using the existing
invariance theorem for an actual equivalence of pairs.
`Correspondence.parameterEulerPolynomial` specializes it to the actual local
inertia group and published geometric Frobenius lift, after forgetting the
parameter conditions and rank certificate.

The theorem `parameterEulerPolynomial_natDegree_eq_rank_iff` identifies degree
`n` with exactly `IsUnramifiedParameterClass F D`. The forward proof chooses a
representative of the underlying pair class, uses its rank certificate, and
applies the invariant-kernel degree criterion. That criterion gives zero
monodromy and trivial inertia. The representative is then isomorphic to its own
underlying representation with zero monodromy. The reverse proof applies the
same degree criterion to the zero-monodromy representative supplied by the
unramified predicate and transports the polynomial and rank through its class
equality.

No continuity or Frobenius-semisimplicity hypothesis is added. The latter is
already part of the type of the input parameter class and is not needed by this
linear-algebra deduction. This file proves neither the automorphic spherical
degree criterion nor `FullCorrespondenceUnramifiedStatement`.
