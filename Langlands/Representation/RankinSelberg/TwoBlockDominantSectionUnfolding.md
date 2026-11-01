# Section unfolding with compact diagonal norm support

This derived helper constructs the actual product of a standard Whittaker
function and the scalar value of a normalized lower section on the quotient
by the two block upper-unipotent groups. A scalar weight on the standard
unipotent quotient is retained. Block covariance cancels the standard and
inverse characters, so the function descends without a selected representative.
On a radical fiber the integrand is the test value times the ordinary raw
Jacquet integrand times the weight.

The signed and absolute radical averages are continuous whenever the test and
weight are continuous. The smooth section makes the entire raw Jacquet
integrand locally constant in the group variable; applying the signed or norm
integral preserves that local constancy. The absolute average uses the integral
of the raw norm rather than the norm of the signed Jacquet integral.

On a fixed determinant slice, compact support of the test norm implies compact
support of the absolute radical average. Clopen restriction and continuity give
its integrability against every compatible standard quotient measure.
Ordinary absolute Jacquet convergence separately supplies actual integrability
on every radical fiber. The published normalized radical kernel tower then
gives actual block-quotient integrability, integrability of the signed average,
and the first unfolding formula with the supplied rectangular integral-cube
mass. No inference from equality of total integrals to convergence is used.

The compact-support premise is intended to be discharged by
`diagonalWhittaker_slice_hasCompactSupport` for diagonal restrictions from a
strictly larger rank. The helper itself permits any test satisfying that
premise. It asserts neither lower-kernel convergence nor the final Laurent
identity. This is derived infrastructure for JPSS (1983), Sections 4.6,
4.9 and 4.10(2), using the published Section 4.5 support route.
Source: `jpss-1983-rankin-selberg`, retained PDF SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
