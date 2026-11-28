# Change of variables along upper-corner conjugation

Let \(e\) be an idempotent in a finite-dimensional algebra \(A\).
Write \(M\) for its centralizer and \(U=eA(1-e)\). The map
`upperCornerAdjoint` sends \(Z\in U\) to \([Y,Z]=YZ-ZY\) for \(Y\in M\).
If \(X\in M\) is regular in \(A\), its adjoint map on the full
off-diagonal summand is injective. Its restriction to \(U\) is then
injective and hence bijective by finite dimension.

In a normed algebra over a proper nontrivially normed field, start
with additive Haar measure \(\mu\) on \(U\).
`idempotentParabolicOrbitChange` constructs one additive Haar measure
\(\nu\) equal to the pushforward of \(\mu\) by \([Y,\cdot]\) for every
\(Y=m^{-1}Xm\) with \(m\in M^\times\). For a measurable complex
function \(f\) on \(A\), the corresponding Bochner integral identity is

\[
  \int_U f\bigl((1-Z)Y(1+Z)\bigr)\,d\mu(Z)
    = \int_U f(Y+Z)\,d\nu(Z).
\]

## Proof

The measure \(\nu\) is the pushforward by the linear automorphism
\([X,\cdot]\). Conjugation \(C:Z\mapsto m^{-1}Zm\) is another linear
automorphism of \(U\), and \([Y,\cdot]=C[X,\cdot]C^{-1}\).
The pushforwards of \(\mu\) by \([X,\cdot]\) and \(C^{-1}\) are scalar
multiples of \(\mu\) by Haar uniqueness. The two scalars commute, so
in the pushforward by \([Y,\cdot]\) the maps \(C^{-1}\) and \(C\) cancel
and the remaining measure is \(\nu\). The identity
`upperCornerUnit_inv_conj` now gives the integral formula by the
change of variables for a pushforward.

## Source

This is the upper-corner instance of the unipotent change of variables
in Lemma 1.6 of Harish-Chandra, *Admissible invariant distributions on
reductive p-adic groups*, University Lecture Series 16, 1999,
§1.2, pp. 7–8. The formula uses the pushforward Haar measure
directly, absorbing the Jacobian into its normalization.
