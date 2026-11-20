# Right differentiation of smooth archimedean vector functions

For a number field `F`, a natural rank `n`, and a normed complex vector space
`V`, this module constructs `realVectorSmoothLieAction` on the existing
`VectorSmoothFunctions F n V`. The action assigns the real matrix Lie algebra
element `X` the complex-linear endomorphism `vectorSmoothDifferential F n X`.
In mixed matrix coordinates its evaluation at a group point `g` is

\[
(D_X f)(g)=d\widetilde f_g(gX),
\]

where `g` and `X` on the right are their coordinate matrices and
`vectorCoordinateExtension` gives the chart expression \(\widetilde f\).
Differentiation uses the underlying real vector space of `V`. The direction
\(gX\) gives the differential of right translation.

The units chart identifies the matrix group with an open subset of ambient
matrices. The proof composes with the smooth chart inverse on that open
subset to obtain local smoothness at every unit. Two chart expressions that
agree on the units have the same derivative at each unit by
`Filter.EventuallyEq.fderiv_eq`. Applying `ContDiffAt.fderiv_right` and
evaluating on the smooth field \(h \mapsto hX\) gives smoothness of \(D_X f\).
Linearity of differentiation gives the complex endomorphism and its
real-linear dependence on `X`.

The chain rule shows that \(D_X\) commutes with postcomposition by a
continuous complex-linear map and with pullback under left multiplication.
It also gives `vectorSmoothDifferential_hasDerivAt` for any supplied
real-parameter curve through the identity with matrix tangent `X`. For
the Lie law, the proof identifies the bracket of the fields
\(h \mapsto hX\) and \(h \mapsto hY\) with \(h \mapsto h(XY-YX)\) and applies
Mathlib's `VectorField.fderiv_apply_lieBracket` to the chart expression.

This is an internal extension of the scalar construction in
[`ArchimedeanSmoothDifferential`](ArchimedeanSmoothDifferential.md) and the
scalar operator laws in
[`ArchimedeanDifferentialLawsProof`](ArchimedeanDifferentialLawsProof.md).
The latter pair supplies the chart convention and sign. The vector space and
smooth postcomposition come from [`ArchimedeanVectorSmooth`](ArchimedeanVectorSmooth.md).
The extension supplies the coefficient-map and left-pullback laws needed
to differentiate the covariance relation of smooth adelic block sections.
