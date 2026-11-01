# Signed unipotent orbit Fourier exchange

This internal result is the signed representative version of the published
unsigned orbit Fourier exchange. It is derived from the same bilinear
rectangular Fourier identity, framed product integrability, and the exact
signed reflection from `SignedReflection`.

The dual kernel is `χbar(u) * Φhat(iota(u) * W⁻¹ * X) * Ψ(X)`.
The original kernel is `χbar(u) * Φ(X) * Ψhat(W * u⁻¹ * X)`.
Both use the same supplied additive Haar measure on all matrix coordinates
and the same actual unipotent Haar. The first test has invertible ambient
support for original-kernel convergence. The second test has support in the
positive-level box for dual-kernel convergence; its first-column frame is
invertible even when the matrix itself is singular.

For dual convergence, the ordinary framed integral uses the inverse standard
character and the left translate of `Φhat` by `W⁻¹`. The signed reflection
preserves this phase and the Haar measure exactly. For original convergence,
the framed integral uses the standard character, the left translate of
`Ψhat` by `W`, and the first test's invertible support. Inversion changes the
phase to the inverse character and preserves the unipotent measure.

At a fixed unipotent, bilinear Fourier exchange uses the factor
`B = iota(u) * W⁻¹`. It has determinant norm one, as follows from the
unipotent determinant, the unsigned Weyl permutation, and the involutive
alternating diagonal. Its Fourier partner factor is exactly `W * u⁻¹`.
Fubini then equates the full product integrals after both absolute
convergence statements have been proved. The results allow every natural
rank parameter and every supplied self-dual measure and character.
They do not assert the matrix-to-rank-one gamma comparison.
