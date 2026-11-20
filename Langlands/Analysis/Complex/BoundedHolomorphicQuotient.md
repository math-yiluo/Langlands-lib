# Interior growth of a holomorphic quotient of bounded functions

`BoundedHolomorphicQuotientDiskGrowth` concerns holomorphic functions \(G,H\) on the unit disk with \(G(0)\ne 0\) and both \(G\) and \(GH\) bounded in norm by one. It bounds \(H(w)\) by
\[
\exp\!\left(\frac{5(1-\log |G(0)|)}{1-|w|}\right).
\]
The statement uses the product so it applies at any zeros of \(G\) as well.

The proof chooses a radius \(R\) strictly between \((1+|w|)/2\) and one at which \(G\) has no zeros on the circle, using finiteness of the divisor on a slightly larger closed disk. Mathlib's `MeromorphicOn.exists_ecanonicalDecomp` removes the zeros of \(G\) inside the circle. The resulting holomorphic nonvanishing factor has the same modulus as \(G\) on the circle and modulus at least \(|G(0)|\) at the origin. The maximum modulus principle bounds the factor and its product with \(H\) by one on the smaller disk. The real part of a holomorphic function on this disk equals the logarithm of the modulus of the factor. Applying Mathlib's `Complex.borelCaratheodory_zero` to this holomorphic function minus its value at zero bounds the variation of that real part, giving the stated upper bound for \(H\).

This is a derived estimate from the existing canonical decomposition, harmonic conjugate and Borel–Carathéodory theorems. It supplies the disk estimate needed to transfer exponential strip growth of numerator and denominator to the holomorphic quotient in the Rankin–Selberg continuation.
