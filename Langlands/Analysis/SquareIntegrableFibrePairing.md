# Integration and pairing of square-integrable fibres

`memLp_two_integral_fst` takes a jointly square-integrable function for
`α.prod μ`, where the parameter measure `α` is finite and the common
measure `μ` is s-finite (a countable sum of finite measures). It proves
square integrability for `μ` after integrating out the parameter. On
almost every fibre, Cauchy–Schwarz bounds the squared norm of the integral
by the mass of `α` times the integral of the squared norm. Fubini gives
integrability of this bound and almost-everywhere strong measurability
of the fibre integral.

`SquareIntegrableFibrePairingStatement` takes two families that are
jointly square integrable for `α.prod μ` and `β.prod μ`, where `α` and
`β` are finite and `μ` is s-finite. The fibrewise pairing over `μ`,
with the second factor conjugated, is integrable for `α.prod β`. Its
iterated integral over the two parameter measures equals the pairing
over `μ` of the two parameter integrals.

The proof `squareIntegrableFibrePairing` pulls the two families back
to the product of the three measured spaces. Each pullback is square
integrable because the added measure factor is finite. Hölder's
inequality gives integrability of the product with the second factor
conjugated, so Fubini gives the equality between the two orders of
integration.

These are the finite-measure Fubini steps used after the split-centre
Fourier transform in E. Lapid, *On Arthur's asymptotic inner product formula
of truncated Eisenstein series* (2011), §8, printed p. 328 (volume PDF p. 337).
The spectral weights are compactly supported, so their noncentral
coordinate measures can be restricted to compact sets.
