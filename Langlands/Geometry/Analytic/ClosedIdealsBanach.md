# Closed ideals from finite generators and an actual geometric inverse

Author: Worker 56.

Let A be a complete Noetherian normed commutative algebra over a
nontrivially normed field K. The theorem proves that every actual ideal
of A is closed.
Neither completeness of K nor an ultrametric hypothesis on K or A is
required. The result applies to commutative Noetherian Banach algebras
with the stated normed scalar structure.

For an ideal I, its topological closure is a closed submodule of A
and hence complete. Noetherianity supplies a finite generating family
for this closure. The resulting continuous surjection from a finite
product of A is a quotient map; the Banach open mapping theorem supplies
preimages with a uniform linear norm bound.

Each generator is approximated by an element of I. The error is lifted
to a coefficient vector small enough that the sum of the norms of all
these vectors is less than one. They define an actual continuous linear
operator F on the finite product with operator norm less than one.
Mathlib's convergent geometric-series construction gives the unit
one minus F, including its inverse.

Applying the generator map after one minus F is exactly the linear
combination map for the approximating elements of I. Since one minus F
is surjective, every element of the closure belongs to I. The equality
with the topological closure proves closedness.

This implements the closure argument in Proposition 2.3.4, page 6,
of the retained Berkovich-course notes. The source uses a small matrix
and its inverse; the Lean proof uses the same coefficient data as a
continuous linear endomorphism and constructs its inverse by the
geometric series. The result is stated for Noetherian Banach algebras
because the argument uses precisely these hypotheses. It does not
assume a closed ideal or an inverse matrix as input.

Source: `provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
retained PDF SHA256
`c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
