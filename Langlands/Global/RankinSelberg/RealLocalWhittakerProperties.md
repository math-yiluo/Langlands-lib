# Regularity of every right derivative in the real coefficient model

This internal supporting result for Task 7400 is in namespace
`Langlands.Global.RankinSelbergGlobal`. It proves
`RealLocalWhittakerRegularityStatement` for the specified coefficient space
`realWhittakerModel`. It supplies the regularity hypotheses needed by a
future gauge or convergence estimate. It proves neither convergence nor a
functional equation.

The namespace `RealLocalWhittaker` contains the following definitions.
`HasPolynomialGrowth W` asks for a bound
`‖W g‖ ≤ C * realMatrixHeight g ^ N` with a nonnegative real `C` and a
natural `N`. `regularFunctions r a` is the complex subspace of smooth
functions on `GL_(r+1)(ℝ)` that satisfy this bound and have left
upper-unipotent character `realWhittakerCharacter a`.
`iteratedRightDerivative r Xs W` composes the real matrix-model right
derivatives specified by a finite list of matrix directions. The first
direction acts after the derivatives in the tail.

`model_le_regularFunctions` proves that every function in
`realWhittakerModel r ds a` belongs to this regular-function space. Each
generating range has these properties by the first three clauses of its
coefficient intertwiner. Smoothness and left covariance are preserved by
complex linear combinations. Polynomial bounds are also preserved:
constants add, a scalar multiplies the constant by its norm, and a sum
uses the maximum of the two exponents. The height is at least one in the
positive matrix size `r+1`, by `two_le_realMatrixHeight`. Replacing an
intertwiner's possibly negative bound constant by its maximum with zero
supplies the explicitly nonnegative convention used here.

`rightDerivative_mem_model` proves stability under an arbitrary real
matrix right derivative. For a generating function `B f`, the published
real standard-module Lie action gives a source vector
`f' = realStandardLie (1 ⊗ X) f` whose underlying function is the right
derivative of `f`. The last clause of `IsRealWhittakerIntertwiner` then
identifies the right derivative of `B f` with `B f'`, still in the same
model. To extend from ranges to their supremum, the proof forms the
submodule of smooth functions whose derivative lies in the model.
The Library's additivity and complex homogeneity of right derivatives
on smooth functions make this a submodule. Inclusion of every generating
range therefore gives the desired inclusion of their supremum.

List induction gives `iteratedRightDerivative_mem_model`.
`realLocalWhittakerRegularity` combines this with
`model_le_regularFunctions`: every iterated derivative is smooth, has the
same left character, and has a polynomial height bound. The constant and
exponent may depend on the function and on the entire finite list of
directions. In particular the result applies to all finite words in the
matrix units, as required by the proposed gauge-estimate route.

The argument uses the already published real standard-module
`(g,K)` action and its derivative formula, and the internal coefficient
model and height estimates. Worker 5665's complex-place model organization
informed the reused real model definition. This proof uses no external
analytic theorem and establishes no new global-to-local model membership.
