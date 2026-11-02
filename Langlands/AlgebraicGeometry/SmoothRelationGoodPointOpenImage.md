# Lifting simple integer coordinates through an open spectral image

This internal auxiliary construction extends the polynomial prime-choice result
of [SmoothRelationGoodPointChoice](SmoothRelationGoodPointChoice.md). All
declarations are in `Langlands.AlgebraicGeometry.SmoothRelationGoodPoint`.

Let `A`, `B` be commutative rings, `ι` an arbitrary index type, and
`Φ : MvPolynomial ι A →+* B`. Let `O` be a subset of `PrimeSpectrum B` whose
image under `PrimeSpectrum.comap Φ` is open, and let `q ∈ O`. The theorem
`exists_prime_simpleIntegerRoots_of_openImage` produces a prime `r ∈ O` such
that its contraction along `Φ.comp MvPolynomial.C` equals that of `q`, and,
for every `i : ι`, there is an integer polynomial `P` with

- `aeval (Φ (MvPolynomial.X i)) P ∈ r.asIdeal`;
- `aeval (Φ (MvPolynomial.X i)) P.derivative ∉ r.asIdeal`.

Thus the coordinate image is a simple root of an integer polynomial modulo the
chosen prime, while the base prime in `A` is preserved. Only the spectral image
is required to be open; the theorem imposes no separate openness assumption on
`O`. It has no finite-index, finite-type, flatness or etaleness hypothesis. The
universes of `A`, `B` and `ι` are independent.

The image of `q` has a polynomial basic open neighborhood contained in the
image of `O`. The imported theorem `exists_prime_simpleIntegerRoots` supplies
a prime in that basic open with the same contraction to `A` and the required
integer equations for the polynomial variables. Membership in the image of
`O` lifts this prime to some `r ∈ O`. Contraction of ideals transports the base
prime equality. Compatibility of integer polynomial evaluation with `Φ`
transports both equation membership and derivative nonmembership.

`SimpleIntegerRootOpenImageData Φ O q` stores an actual chosen prime, its
membership in `O`, the base contraction equality and the coordinate equations.
`simpleIntegerRootOpenImage` constructs this data by classical choice from the
proved existence theorem.

Worker 303 designed the surrounding good-point route using an open spectral
image of etale coordinates. Worker 101 implemented this generic algebraic
lifting step by composing the existing polynomial prime-choice construction
with the basic open basis and image membership. This is an internally derived
prerequisite, with no external source theorem assumed. Establishing the open
image for the chosen coordinates and transporting the resulting prime to a
scheme orbit remain separate geometric obligations; this module does not
assert existence of a good point or the global slicing theorem.
