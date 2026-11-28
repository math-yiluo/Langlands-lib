# Fourier transform of the idempotent parabolic constant term

Let \(e\) be an idempotent in a finite-dimensional algebra \(A\) over
a characteristic-zero nonarchimedean local field \(F\). Write \(M\)
for its centralizer, \(U=eA(1-e)\), and \(L=(1-e)Ae\). The map
`parabolicFourierCoordinates` sends \(((Y,Z),W)\) to \(Y+Z+W\).
Its inverse uses the diagonal and the two corner projections.
`parabolicFourierHomeomorph` gives the same isomorphism with the
module topologies.

For an additive Haar measure \(\nu\) on \(U\), the unaveraged
constant term `parabolicConstantTerm` takes a Schwartz–Bruhat
test \(f\) on \(A\) to the Schwartz–Bruhat test
\[
  g_f(Y)=\int_U f(Y+Z)\,d\nu(Z).
\]
It is the restriction to the upper triangular subspace followed by
`SchwartzBruhat.partialIntegral`.

With a nontrivial unitary additive character and an invariant
nondegenerate pairing \(B\), fix additive Haar measure \(\mu\)
on \(A\). `idempotentParabolicFourier` chooses additive Haar
measure \(\mu_M\) on \(M\), independent of \(f\), such that
\[
  g_{\widehat f}(Y)=\widehat{g_f}(Y).
\]
The ambient transform uses \(B,\mu\), and the Levi transform
uses the restriction of \(B\) and \(\mu_M\).

## Proof

The pairing between \(U\) and \(L\) gives a perfect bicharacter by
`opposite_corner_nondegenerate` and
`isPerfectBicharacter_of_nondegenerate`. Give \(L\) the measure dual
to \(\nu\) for this bicharacter. Haar uniqueness rescales the measure
on \(M\) so that the product on the three coordinates maps to \(\mu\).

For fixed \(Y\), multiply the test in block coordinates by the Levi
character of the diagonal variable. Integrate over the diagonal and
upper variables to obtain a Schwartz–Bruhat function \(W_Y\) of the
opposite variable. The identity `pairing_add_corners` and Fubini show
that the ambient Fourier transform at \(Y+Z\) is the opposite-corner
Fourier transform of \(W_Y\), evaluated at \(Z\). Integrating in \(Z\)
recovers \(W_Y(0)\) by Fourier inversion for dual measures. A second
application of Fubini identifies \(W_Y(0)\) with the Levi Fourier
transform of \(g_f\) at \(Y\).

## Source

This is Lemma 1.4 in Harish-Chandra, *Admissible invariant
distributions on reductive p-adic groups*, University Lecture
Series 16, 1999, §1.2, pp. 6–7, for the parabolic attached to an
idempotent in the unit group of a semisimple local algebra.
