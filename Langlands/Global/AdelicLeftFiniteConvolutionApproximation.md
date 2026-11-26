# Approximation of a right translate by left-finite convolutions

The left-finite test functions form the complex submodule
`leftFiniteTestFunctions`. The sum of the spans of two finite left orbits bounds
the span for their sum. Scalar multiplication preserves the finite span, and
the intersection of two open finite-adelic subgroups gives a common level.

`exists_leftFinite_convolution_approximation` takes the Library's
`RightTranslationTestFunctionSeparationStatement` as a premise. For a
continuous left-rational-invariant function on the adelic group, assume both
its descent to the rational quotient and its left-finite convolutions belong
to the quotient `L²`. Convolution against the fixed function defines a linear
map from the test submodule to `L²`. Continuity and the compact kernel support
justify linearity of the pointwise integrals.

Every vector orthogonal to the range of this map has zero pairing with all
such convolutions. Apply the separation premise at the inverse of the desired
translating element. The unitary right action on the quotient then identifies
the separated pairing with the inner product against the desired right
translate. The double orthogonal is the norm closure of the range. Taking one
vector from this range gives one kernel, and the almost-everywhere formulas
for the quotient action and the `L²` representatives give the claimed
`eLpNorm` bound on the exact Haar quotient.

`leftFiniteConvolutionApproximation` packages the implication as
`LeftFiniteConvolutionApproximationStatement` for the exact left-finite test
function predicate. This is an internal consequence of the quotient right
action, the separation statement, and the double-orthogonal theorem for
Hilbert spaces. It concerns the convolution range of a single input function.
