# The finite Iwasawa expansion in partial convolution form

Fix a standard parabolic \(P=MU\) in a compatible standard family over
a number field, with a positive point map \(p\) into the Levi.
`leviFibrePairingExpansionIntegrand` is the positive-variable integrand
in one summand of a Levi pairing. It uses a compactly supported
continuous ambient kernel \(\beta\), a function \(f\) on the Levi, a
test \(t\) on the positive rational quotient, and an ambient parameter
\(g\). At \(b\) it is
\[
  \delta(p(b))^{-1}\int_{M(F)\backslash M(\mathbb A)^1}
      f(p(b)y_q)\,\overline{\Theta_t[L(g,p(b)\,-)](y_q)}\,dq,
\]
where \(L(g,m)=\operatorname{radicalKernel}(\beta,g,1,m)\)
and \(\Theta\) is the norm-one partial convolution. For each quotient
point \(q\), \(y_q\) is the image of Lean's chosen representative
`Quotient.out q`. The definition accepts arbitrary \(f\) and \(t\).
The integrals are Mathlib's Bochner integrals, which take value zero
on nonintegrable integrands.

`exists_leviPairing_rightConvolution_eq_fibreExpansion` fixes a
positive-size ambient matrix representation and an Iwasawa compact.
It obtains the positive Iwasawa measure factor and applies the finite
unfolding for a continuous, left invariant input of height growth
with a finite right compact expansion. The test is continuous and
rationally invariant with weighted norm-one representatives. The
compact majorant supplies absolute domination. The test is transported
from the norm-one quotient to the positive rational quotient using
the central split torus comparison. The inner kernel integral of
each summand is the conjugate of the partial convolution of that
transported test. In this application, the rational invariance of
the Levi fibre and the partial convolution make the quotient
integrand independent of the choice of representative. The
continuity, invariance, height growth and weighted representative
hypotheses give the product-integrability estimates used to unfold
the pairing.

The recentering theorem takes the ambient parameter
\(\iota(p(a))g\). The left-invariant positive Haar measure permits
the change of variable \(b\mapsto ab\). Left-Levi covariance contributes
\(\delta(p(a))\), which cancels its inverse in the weight. Centrality
allows \(p(a)p(b)\) to move to the right in the argument of \(f\).
The convolution is then by \(L(g,-)\) and evaluated at \(y p(b)\),
giving the scalar integral used by the finite Bochner vectors.
This identity keeps the same chosen representatives and uses the
totalized integrals for arbitrary \(f\) and \(t\).

These are internal formulas for the norm-one pairing characterization
of Bernstein–Lapid, *On the meromorphic continuation of Eisenstein
series*, §6.2, equation (6.8), with the parabolic Iwasawa measure of
Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series*,
I.1.13.
