# Fourier transforms of finite orbital measures

`FiniteOrbitalFourierStatement` concerns the orbital distribution of an
element \(X\) of a finite-dimensional algebra over a nonarchimedean
local field. Write \(H\) for its stabilizer in the unit group \(G\)
and let \(\nu\) be a finite Borel measure on \(H\backslash G\).
Every Schwartz–Bruhat orbital integrand is integrable for \(\nu\):
the test function is bounded and its pullback along the continuous
orbit map is measurable.

For the pairing \(B\), character \(\psi\) and additive Haar measure
used in the Fourier transform, `finiteOrbitalFourier` proves that
the Fourier-transformed distribution is integration against
\[
 \Theta(Y)=\int_{H\backslash G}\psi(B(g^{-1}Xg,Y))\,d\nu(Hg).
\]
The integrand has norm one. Dominated convergence proves continuity
in \(Y\), and the integral norm bound gives
\(\|\Theta(Y)\|\le \nu(H\backslash G)\).
The joint kernel after multiplication by a test \(f(Y)\) is
measurable and has norm \(|f(Y)|\), which is integrable for the
product of the finite quotient measure and additive Haar.
Bochner Fubini gives the distribution identity.

This is the finite-measure calculation from the definitions of the
orbital distribution and its Fourier transform in Harish-Chandra,
*Admissible invariant distributions on reductive \(p\)-adic groups*,
Introduction, printed pp. 2–3. It gives the local summability
conclusion of Theorem 1.1 when the stabilizer quotient has finite
measure, in particular for a regular quotient measure on a compact
stabilizer quotient.
