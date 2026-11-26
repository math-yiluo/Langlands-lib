# Oscillatory terms tested inside their smooth parameter domain

`SchwartzFourierOscillationStatement` concerns a finite sum of oscillatory
integrals on a finite-dimensional real inner product space with its canonical
Lebesgue measure. The smooth compactly supported test \(a\) has topological
support inside an open set \(U\). Each coefficient \(c_i\) is smooth on \(U\).
The \(i\)-th term is
\[
b_i(t)\int e^{2\pi i\langle y,\xi_i(t)\rangle}\,a(y)c_i(y)\,dy.
\]
Along the supplied filter, the real scale \(r(t)\) tends to \(+\infty\).
For each summand, eventually \(\|\xi_i(t)\|\geq \kappa_i r(t)\) and
\(\|b_i(t)\|\leq B_i r(t)^{d_i}\), where \(\kappa_i>0\), \(B_i\geq 0\), and
\(d_i\) is a natural number. The finite sum tends to zero.

`schwartzFourierOscillation` proves this by forming the Schwartz function
\(a c_i\). On the support of \(a\), smoothness follows from smoothness of
both factors on \(U\). At every other point the product vanishes in a
neighborhood. Its inverse Fourier transform is again Schwartz, with the
positive phase in the display. A bound of degree \(d_i+1\) on this transform
bounds the norm of the \(i\)-th term by a constant times \(1/r(t)\) eventually.
The proof takes limits termwise in the finite sum.

This is the Fourier estimate used in Delorme, *On the spectral theorem of
Langlands*, Advances in Mathematics 426 (2023), 109107, Lemma 7.6, p. 32.
On a generic open parameter region, (7.12) expresses each term as an
exponential at the Weyl-transformed projected truncation parameter times
coefficients that are smooth on the region and polynomial in the truncation
coordinates. The factors from the polynomial derivatives of the denominator
can be included in \(c_i\); a fixed central translate is absorbed there as
well. The estimate applies to summands for which the resulting phase vector
obeys the stated lower bound, with a fixed real phase independent of the
test variable allowed in \(b_i\). The truncation geometry establishing that
bound is separate from the Fourier argument.

The source is the published PDF in `delorme-2023-spectral-theorem-langlands`,
SHA-256 `9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`.
Its positive kernel is in (7.10), p. 25. The factor \(2\pi\) in the theorem
is Mathlib's Fourier convention.
