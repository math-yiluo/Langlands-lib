# Actual infinite adelic differentiation on the original smooth functions

This is an internal construction specializing
`Langlands.Geometry.Manifold.groupDirectionalValue` to the actual infinite
adelic group and its constructed real smooth atlas. It imports the proved
manifold interpretation of the original plot-smooth predicate. It does not
transcribe a new assertion from external literature.

Fix a number field `F` in an arbitrary universe and an affine group scheme `G`
over `F`. Given `hsmooth : SmoothOfRelativeDimension d G.X.hom`, use the
specified completion scalar structures, `smoothChartedSpace F G hsmooth`, and
its proved smooth group structure. The tangent directions belong to
`GroupLieAlgebra` for this atlas, namely its real tangent space at the identity.
This tangent is definitionally the model `smoothModel F d` used in the
pointwise formulas.

## Differential on the unchanged function carrier

`plotSmoothDifferential F G hsmooth X` is a complex-linear endomorphism of the
existing `G.plotSmoothFunctions` submodule on
`InfiniteAdelicGroupPoints F G`. Its coefficient map to mixed coordinates is
the original `InfiniteAdeleRing.ringEquiv_mixedSpace F`. No new function carrier
or substituted action is used. Its pointwise formula, recorded in
`plotSmoothDifferential_apply`, is

```text
(D_X f)(g) = mvfderiv I (fun h => f (g * h)) 1 X,
I = 𝓘(ℝ, smoothModel F d).
```

Thus it differentiates the positive right orbit using the actual group
multiplication and the actual identity tangent. The derivative is real in its
tangent variable although the functions and their endomorphisms are complex.

For closure, `isPlotSmooth_iff_contMDiff` first turns the original membership
proof into ordinary real smoothness in this atlas. The generic
`contMDiff_groupDirectionalValue` then gives smoothness of the derivative;
the reverse implication of the same criterion returns membership in the
original submodule. The endomorphism's addition and complex-scalar laws follow
pointwise from the corresponding generic differential laws on smooth
functions, followed by subtype extensionality.

`realPlotSmoothDifferential` bundles the dependence on `X` as a real-linear map
from the identity tangent into these complex-linear endomorphisms. The proof
uses pointwise linearity of the actual manifold derivative in its tangent
argument and extensionality of the endomorphisms and function subtypes.

## Actual left pullback and reductive specialization

`plotSmoothLeftTranslation F G a` is the complex-linear endomorphism
`f ↦ (g ↦ f (a * g))` on exactly the same submodule. Its closure uses the
original `GroupScheme.IsPlotSmooth.leftTranslate` result. The application
lemma records this literal pullback formula.
`plotSmoothDifferential_leftTranslation` proves that this pullback commutes
with `D_X`. After subtype extensionality it is the generic orbit identity,
which follows from associativity of the original multiplication.

`reductiveRealPlotSmoothDifferential F G hG` specializes the real-linear map
to the exact `reductiveChartedSpace F G hG`. The algebraic
`GroupScheme.IsConnectedReductive G` predicate supplies the already proved
constant relative dimension `hG.smoothDimension_spec`; no additional chosen
analytic smoothness premise is imposed. The surrounding affine instance is
retained as in the general construction.

This unit constructs first-order differentiation on the infinite adelic smooth
functions. It does not assert a Lie-bracket or universal-enveloping-algebra
extension, an exponential-curve comparison, derivative growth estimates, or
differentiation of adelic rational-invariant functions across finite slices.
Those further constructions and the comparison with the original matrix
`GL_n` differential remain separate obligations.
