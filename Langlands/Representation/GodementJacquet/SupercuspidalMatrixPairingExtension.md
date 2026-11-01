# Extending Fourier-regular pairing identities to arbitrary tests

This internal derivation combines compact supercuspidal conjugate smoothing,
bilinear compact transfer, and the spanning theorem for actual integrated cutoff
outputs. It introduces no new analytic integration or functional equation.

`fourierRegularMatrixPairingRestriction` is the complex linear restriction map
from bilinear pairings on full-matrix Schwartz–Bruhat tests and representation
vectors to pairings whose test variable lies in the actual Fourier-regular
submodule. The codomain of a pairing is an arbitrary complex module; it needs no
topology. Field, representation, and codomain universes are independent.

Suppose the representation is irreducible and supercuspidal, its inverse-transpose
pullback is supercuspidal, and its rank is `m + 1` with `0 < m`. Assume a pairing
satisfies the explicit determinant-norm-one translation rule
`B(rectangularTranslate g Φ, w) = B(Φ, ρ(g⁻¹)w)`. If its Fourier-regular restriction
is zero, then it is zero everywhere. For fixed `Φ`, its vector-variable kernel
contains every integrated conjugate-cutoff output: compact transfer identifies
the pairing at that output with the pairing at the conjugately smoothed test,
which is Fourier-regular. The output span is the whole representation by
irreducibility, so this kernel is top.

Applying this vanishing result to the difference of two pairings proves that
two pairings satisfying the same translation rule are equal whenever their
Fourier-regular restrictions are equal. In applications the codomain may be
complex rational functions, so postcomposition by fixed complex linear maps and
multiplication by a fixed rational function fit without any convergence exchange.
