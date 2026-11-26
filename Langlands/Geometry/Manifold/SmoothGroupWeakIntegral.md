# Invariant differential equations for integrals tested against compact supports

`SmoothGroupWeakIntegralStatement` concerns a finite combination of words in invariant
derivatives on a finite-dimensional real Lie group. Its smooth multiplication and inversion
are taken in the specified charts. The group is Hausdorff, locally compact and sigma-compact,
with its Borel measurable structure. The group measure is right invariant, finite on compact
sets and positive on nonempty open sets. Both the group measure and the parameter measure are
s-finite.

The integral is assumed smooth. Each smooth integrand satisfies the same differential equation,
and multiplying the integrand by a continuous compactly supported test function gives an
integrable function on the product of the group and the integration space. The integral
satisfies the differential equation.

The proof first differentiates the right-translation identity for Haar integration of a
smooth compactly supported function. Its translates in a compact neighborhood of the
identity have support in one compact set, so `compactManifoldIntegrableWeight` gives the
derivative. The derivative of the integrand is supported there because invariant
derivatives preserve topological support. This identity gives integration by parts
for each invariant derivative. Reversing the word and inserting a minus sign at each
step gives a compactly supported transpose for the bilinear integral pairing.
Adding the transposed tests with the original word coefficients gives the
test for the full differential operator.

Fubini transfers the equation from each integrand to the tested integral. A nonzero smooth
function can be detected by such a test. On a relatively compact neighborhood where a
constant complex rotation makes its real part positive, a nonnegative smooth bump gives a
strictly positive real integral.
