# Bilinear rational values of actual matrix integrals

This internal construction packages supplied actual shifted rational values as
a complex bilinear map. It derives no new rationality or convergence theorem
from a representation hypothesis. Its provenance is linearity of the actual
matrix integrand and Bochner integral, the coefficient closure in `ZetaLinear`,
and the published uniqueness and linear closure of rational continuation.

The first group of lemmas supplies linearity in the full Schwartz–Bruhat matrix
test. At a fixed exponent, integrands add and scale. Convergence is closed under
these operations. The integral is additive when the two original integrands
are integrable, and commutes with complex scaling without a convergence
hypothesis. The zero test has rational value zero for every coefficient.

Addition of actual shifted rational values in the test variable takes the
maximum of their convergence bounds, uses integral additivity on that common
right half-plane, and transfers the sum continuation there. Scaling uses the
constant-multiple continuation theorem. Both conclusions retain convergence
and reduced-denominator nonvanishing on a right half-plane; they do not assert
additivity of totalized divergent integrals.

For an arbitrary complex module `W`, let `C` be a complex linear map from `W`
to functions on the general linear group. The explicit premise `hRat` supplies
an actual shifted rational value for every full-matrix test and every `w : W`.
`matrixRationalValue` chooses such a value, and its specification records both
actual convergence and rational continuation. When `q > 1`, continuation
uniqueness identifies choices with the sums and constant multiples supplied by
the closure lemmas. This defines
`matrixRationalPairing q abv μ C hRat hq`, linear first in tests and then in `W`.
Its codomain is the field of complex rational functions, before evaluation at
any spectral point. Standard linear-map finite-sum and scalar identities
therefore apply without making assertions at poles.

`matrixRationalPairing_spec` retains the actual shifted-rational-value relation
for each value, and `matrixRationalPairing_eq` identifies it with every other
supplied actual continuation. The exponent in that relation is exactly
`s + jpssShift n`; the rational variable is `spectralPoint q s = q^(-s)`.
The field, topology, absolute value and group measure remain arbitrary, and
the coefficient module has an independent universe.

`coefficientIotaLinearMap` is the literal complex linear operation
`f ↦ (g ↦ f(inverseTranspose g))`. For a coefficient submodule, its inclusion
can be used as `C` for the original pairing; composing the inclusion with this
map gives the inverse-transpose pairing on the same source module. This
requires separate supplied rationality for that family and assumes no
identification with a contragredient model.
