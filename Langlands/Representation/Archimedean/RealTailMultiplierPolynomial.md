# Polynomial form of the differential tail multiplier

This internal identity expresses the actual rank-one tail multiplier as
a polynomial on its parity class when its symmetry sign is `(-1)^ell`.
For positive `ell`, reduced parity `epsilon` with
`ell-1 ≡ epsilon (mod 2)`, and every integer `j ≡ epsilon (mod 2)`,
the multiplier equals

`descPochhammer ell ((j+ell-1)/2) / ell!`.

The displayed expression is implemented as `tailPolynomial ell`, of degree
exactly `ell`. At nonnegative `j`, parity arithmetic identifies the natural
upper index in `tailSeq` with `(j+ell-1)/2`. The falling-factorial formula for
natural binomial coefficients then proves the equality. Reflection of the
Pochhammer polynomial gives `p(-j)=(-1)^ell p(j)`; the existing tail symmetry
extends the identity to negative indices.

`RealTailMultiplierPolynomialStatement` collects the degree and parity-class
identity under exactly the positive cutoff, reduced parity and resonance
hypotheses above. `realTailMultiplierPolynomial` proves it.

This is an identity of scalar Fourier multiplier values. It does not yet
identify an actual Frobenius map with polynomial evaluation in a compact
rotation generator or prove any ambient kernel or filtration statement.
