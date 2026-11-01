# Square Fourier exchange with transpose and right multiplication

This internal helper uses the Library's actual plus Fourier integral, with its
entry pairing and the exact square product of the supplied scalar Haar measure.
It proves a scalar integral identity; it does not assert a representation
functional equation or the existence of its scalar factor.

`squareTransposeRightHomeomorph A` sends `X` to `transpose X * A`, for an actual
invertible matrix `A`. Its inverse is `X ↦ transpose (X * A⁻¹)`.

Transposition preserves the product measure and the entry pairing. Consequently
the Fourier transform of `Y ↦ Φ(transpose Y)` at `X` is the Fourier transform of
`Φ` at `transpose X`. The arbitrary determinant scaling theorem for actual
additive Haar measure then gives

`Fourier (Y ↦ Ψ(transpose Y * A)) X
 = |det A|^(-d) * Fourier Ψ (transpose X * inverseTranspose A)`.

Here `d` is the square size, and the absolute value is the supplied p-adic
realization's residue-normalized determinant norm. No determinant-one
hypothesis is used.

Apply the published bilinear Fourier exchange to `Φ` and the pullback of `Ψ`
by the transpose-right homeomorphism. Substitution of the preceding Fourier
transport formula proves

`∫ Fourier Φ X * Ψ(transpose X * A) dX
 = |det A|^(-d) * ∫ Φ X * Fourier Ψ(transpose X * inverseTranspose A) dX`.

The proof uses the existing absolutely integrable two-test exchange and the
existing exact Haar change of variables. All scalars retain the supplied
measure normalization. The argument is an internal derivation from these
published results, and applies to every square size, including zero.
