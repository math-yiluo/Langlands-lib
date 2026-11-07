# Centered block L-polynomial rescaling

`centeredHalfShiftUnit F` is the nonzero complex number `q^(-1/2)` for the
canonical residue cardinality. `CenteredBlockLPolynomialStatement` transports
supplied original and actual inverse-transpose base-pair L-polynomial
certificates to every pair of the existing `centeredSegmentBlocks`.

For indices `i` and `j`, the sum of the real determinant exponents is
`(m+n-2i-2j)/2`. Thus the original polynomial is substituted at
`q^(-(m+n-2i-2j)/2) X`, expressed by `polynomialRescale` and the integer
`blockExponent`. Inverse transpose negates both real exponents, giving the
inverse substitution for the supplied dual polynomial. The dual certificate
uses the negated additive character and the identical underlying Haar measure.
Both rank orders and independent field and carrier universes are retained.

This internal statement combines the Library's unramified-twist transport with
the actual scalar twists defining the centered blocks. It assumes the two base
certificates and asserts no existence theorem, irreducibility, unitarity, or
formula for segment components. Its purpose is to connect those existing
certificates to the explicit products of `SegmentGammaTelescoping`.
