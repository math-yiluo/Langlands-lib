# Orbital integrals and the compactly averaged constant term

In the coordinates of `IdempotentParabolicOrbitalMeasure`, suppose the
pushforward of the Levi quotient, upper-corner Haar and compact Haar
product measure is \(c\) times the ambient orbital measure. Assume the
ambient orbital integrals converge absolutely on Schwartz–Bruhat tests
and the scalar \(c\) is finite.

`IdempotentParabolicOrbitalIntegralStatement` gives absolute convergence
of the Levi orbital integrals on all Levi Schwartz–Bruhat tests. It also
gives, for every ambient test \(f\),
\[
 \mu_X^M(f_P)=c\,\mu_X^G(f),\qquad
 f_P(Y)=\int_N\int_K f(k^{-1}(Y+Z)k)\,d\mu_K(k)\,d\nu(Z),
\]
where \(N=eA(1-e)\), \(\nu\) is the upper-corner Haar in the pushforward,
and \(\mu_K\) is the same compact Haar. The implementation uses the
Schwartz–Bruhat functions `compactConjugationAverage` and
`parabolicConstantTerm` for the two integrations.

For the convergence assertion, ambient convergence first gives finite
ambient orbital mass on compact sets by testing a containing compact
open subgroup. For a compact set \(C\) of Levi elements, choose a compact
neighborhood \(U\) of zero in \(N\). The compact image of \(C\times U\times K\)
under \((Y,Z,k)\mapsto k^{-1}(Y+Z)k\) contains the image of the corresponding
rectangle in the Levi quotient, upper and compact coordinates. Its finite
ambient orbital mass bounds the mass of that rectangle by the pushforward
formula. The upper and compact factors have positive mass. Thus the Levi
orbital measure is finite on compact sets, and every compactly supported
continuous test is integrable against it. The constant-term identity then
follows by integrating along the pushforward and applying Bochner Fubini
in the same coordinates.

Harish-Chandra compares these integrals in *Admissible invariant
distributions on reductive \(p\)-adic groups*, §1.2, printed pp. 7–8.
His computation uses right quotients by the split Cartan component.
The identity here integrates on left quotients by the full unit
stabilizers with the scalar for the supplied Haar measures.
