# Analytic inverse on the high modes of a resonant character pair

This internal construction uses the finite products in `RealBlockMultiplierNormalization`
and their tail specialization in `RealGenericMultiplierDegeneration`. Let
\(\varepsilon\in\{0,1\}\), \(r\geq0\), and \(\ell=\varepsilon+2r+1\). Translate the
regularized multiplier at parameter \(-\ell\) by \(z\), and call it \(R(z,j)\).
It is analytic at \(z=0\) with the canonical reflection symmetry. Away from zero
it equals \(z\) times the generic multiplier at \(-\ell+z\). At zero it is the
canonical tail times its nonzero first high-mode value.

On modes \(j\equiv\varepsilon\pmod 2\) with \(|j|>\ell\), the high inverse is
\(-1/R(-z,j)\). On other modes it is zero. The inverse keeps the original
reflection sign, which is its own inverse, and the mask is invariant under
reflection. At high modes the denominator is nonzero at zero, so each coordinate
is analytic. The reciprocal identity identifies the high inverse with \(1/z\)
times the generic multiplier at \(\ell+z\) on these modes for \(z\ne0\). At zero
its whole parity-class value is the reciprocal canonical tail times the negative
reciprocal of its normalizing scalar, using Lean's totalized inverse on low modes.
