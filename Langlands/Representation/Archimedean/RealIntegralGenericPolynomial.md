# Reciprocal polynomial multipliers on integral generic parity classes

This internal algebraic construction extends the explicit tail polynomial
to the complementary, generic integral parity class. Let `ℓ>0`,
`ε∈{0,1}` and `Even(ℓ-ε)`, and write `Pℓ` for the polynomial of
`RealTailMultiplierPolynomial`. For every integer `j` in the parity class
of `ε`, the result proves

`genericMultiplier ℓ ε j = Pℓ(ε) / Pℓ(j)`.

Both denominator and normalizing numerator are nonzero. The reciprocal
`multiplier ℓ j = Pℓ(j)⁻¹` is recurrent for parameter `ℓ+1` and symmetric
with sign `(-1)^ℓ`. These are actual scalar formulas for the already
defined normalized generic multiplier, including negative Fourier indices.

The proof begins with the falling-factorial shift identity. It gives the
polynomial recurrence

`Pℓ(z+2) (1-ℓ+z) = (z+1+ℓ) Pℓ(z)`.

The product formula for the falling factorial shows that a zero at an
integer `j` would require `j+ℓ-1=2r`, which contradicts the generic parity
`j≡ℓ mod 2`. Inverting the polynomial recurrence and the reflection
formula therefore gives the stated nonvanishing recurrent reciprocal.

For the exact normalization, induction on the nonnegative sequence index
proves `genericSeq ℓ ε m * Pℓ(ε+2m)=Pℓ(ε)`. The two recurrence equations
give the induction step after cancellation of a nonzero denominator.
The existing generic symmetry and polynomial reflection extend this
product identity to negative indices; their signs agree on the generic
parity class and their common sign has square one. Division by the
proved nonzero polynomial value gives the displayed normalized formula.

`generic_frob_relation` also records its direct consequence for an actual
Frobenius map with the normalized generic multiplier: the output Fourier
coefficient multiplied by `Pℓ(j)` equals the input coefficient multiplied
by `Pℓ(ε)`. Off-parity input coefficients vanish by the Frobenius data.

`RealIntegralGenericPolynomialStatement` packages the nonzero normalization,
the recurrence and symmetry of the reciprocal, and the exact normalized
generic-multiplier formula. `realIntegralGenericPolynomial` proves it.
This unit proves no braid identity, identification of a chosen interlaced
equivalence with a particular crossing word, or filtration kernel containment.
