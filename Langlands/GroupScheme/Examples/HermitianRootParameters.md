# Root parameters for a diagonal Hermitian middle form

This internal construction extends the scalar middle coordinate of
`SU3Root.Parameters` to any finite family of diagonal Hermitian coefficients.
It is a prerequisite for the four-variable unitary branch, with two middle
coordinates. It does not assert generation of a unitary group, Witt index,
nondegeneracy, or a classification theorem.

Fix a commutative ring `A`, an involutive ring automorphism `c.bar`, and a finite
index type `ι`. `DiagonalForm c ι` specifies weights `w i` fixed by `c.bar`.
Its pairing is

`h(x,y) = Σ i, w i * x i * c.bar (y i)`.

The pairing is additive in each variable and satisfies
`c.bar (h(x,y)) = h(y,x)`. `Parameters H` is the actual coordinate subtype of
pairs `(x,z)` satisfying `z + c.bar z = h(x,x)`. The implemented group law is

`(x,z) * (y,t) = (x+y, z+t+h(x,y))`,

with identity `(0,0)` and inverse `(-x,c.bar z)`. Conjugate symmetry and
additivity prove that multiplication preserves the equation and is associative;
the equation itself proves inverse cancellation.

The coefficient-change homomorphism applies an involution-compatible ring
homomorphism to every coordinate, assuming it carries each source weight to
the corresponding target weight. Identity and composition are proved.
For every scalar `r` fixed by the involution, `scale r` is the endomorphism
`(x,z) ↦ (r*x,r²*z)`. Scaling by zero is the identity element, scaling by one
is the identity homomorphism, and scaling by a product composes the two
endomorphisms.

The vector projection is a homomorphism to the additive vector group. Its
kernel is central. The commutator convention is `x*y*x⁻¹*y⁻¹`; its vector is
zero and its scalar is `h(x.vector,y.vector)-h(y.vector,x.vector)`.

The construction and proofs are direct algebraic generalizations of the existing
`SU3RootParameters` implementation. They use finite sums and polynomial
identities, with no division or characteristic restriction. All coefficient and
index universes are independent. The middle form may be degenerate and the
finite index type may be empty.
