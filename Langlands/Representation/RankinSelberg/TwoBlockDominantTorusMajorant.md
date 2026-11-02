# A uniform torus majorant for the actual dominant raw kernel

This internal deduction combines the published entry bound for the actual JPSS
five-block matrix, the two rectangle support boxes, the original-torus opposing
cone, and growth of the supplied scalar section. The matrix conventions come
from JPSS (1983), Section 4.10(2), printed page 419. The quantitative majorant is
an internal derived result and asserts no analytic convergence.

`exists_coefficient_rectangle_growth_uniform` chooses the ambient Whittaker
growth base before the complementary rectangle dimensions `j,k`, their rank
equality, and the coefficient-image vector. On nonzero support each rectangle
has exponent `N + torusSize lam`, and the original group argument has exponent
`torusSize lam`. The full matrix bound therefore has exponent
`N + 2 * torusSize lam`. The constant absorbs the fixed power `N`, and squaring
the ambient growth base absorbs the two varying costs. This order of
quantification is needed when one later chooses a convergence threshold before
all complementary rectangle dimensions.

`IsRawKernelTorusMajorant` applies to the unweighted actual kernel at
`blockRotation⁻¹ * torus(lam) * c`, with integral `c`. It bounds its norm by
`C * B ^ torusSize lam * q ^ (-u * twistDegree lam)`, using the opposing twist
and the initial interval determined by the second block. Its base precedes the
twist, section, rectangle dimensions and test vector. For each of these later
inputs, its constants are uniform over torus exponents, integral factors, and
both rectangles. Nonzero raw values imply the opposing cone and simultaneous
membership in the two boxes of exponent `N + torusSize lam`.

The existence proof commutes the inverse block rotation through the torus.
Rotation preserves the sum of absolute exponents and takes integral factors
to integral factors. The coefficient and scalar-section norm bounds multiply;
their bases multiply as well. Nonzero products have two nonzero factors, so
the previously proved original-torus cone and rectangle-box estimates apply.
Independent field and coefficient-carrier universes, arbitrary complementary
dimensions including zero, reducible Whittaker-type representations, and
zero supplied functionals are retained.
