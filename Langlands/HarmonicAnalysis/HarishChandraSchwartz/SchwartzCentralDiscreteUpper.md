# The actual central-image upper inclusion from weight and finite-level estimates

This derived module proves the reverse inclusion of Waldspurger VIII.4.2
for an actual translation-stable Schwartz subspace under explicit weight
estimates and finite compact projected level spans. It preserves the raw
central image and the canonical discrete-series coefficient sum, including
the independent enlarged carrier universe.

`projectedQuotientPositiveFormOfWeights` constructs the actual positive
quotient-L² form. The norm of each function in the projected left-level
representation is square integrable by the central and ambient weight
estimates and compatible-measure transport. Smooth evaluation at one
separates functions, so the actual quotient integral is positive definite.

For a raw-image function, choose a compact open bi-invariance level of a
Schwartz preimage and use its projected left-level right-translation
representation. Finite compact projected level spans give admissibility.
The actual positive form above gives unitarity. Every coefficient of
this admissible function representation belongs to the full raw image:
restriction to a vector's admissible orbit span and Waldspurger I.6.1
identify it with a combination of two-sided translates of that vector.
Central equivariance and translation stability preserve the raw image.
The same norm estimate therefore makes every form coefficient square
integrable, without the source's convolution identity.

The published unitary semisimplicity and irreducible square-integrability
arguments then place its coefficients in the canonical discrete-series
sum. Smooth evaluation realizes the original projected function as one
of those coefficients, without a separate reproducing-vector argument.
Actual carrier lifts give the sum in universe `max uG uW`.

This is an auxiliary upper-inclusion theorem. It constructs the positive
form, admissibility and all coefficient-L² inputs from the displayed
weight and finite-level estimates. The rational closed estimates and
VIII.4.1 are not proved here, and VIII.4.1
(`RationalCuspidalCentralProjectionFiniteStatement`) has no unconditional
proof in the Library; neither of the closed targets
`RationalCuspidalDiscreteCoefficientStatement` and
`RationalCuspidalFixedCoefficientLiftingStatement` (module
`RationalCuspidalCentralStatements`) is asserted here. No measure is
renormalized or replaced by a probability measure.
