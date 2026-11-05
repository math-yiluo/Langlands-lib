# Actual adelic tangents and the original general-linear differential

This is an internal comparison of the constructed actual infinite adelic
manifold with the existing general-linear differential. It uses the original
point maps, mixed matrix coordinates and smooth-function equivalence. It
transcribes no new assertion from external literature.

Fix a number field `F : Type u`, any natural rank `n`, and
`GLG = GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)`.
For the general construction, supply
`hsmooth : SmoothOfRelativeDimension d GLG.X.hom`.
Affineness is the existing general-linear theorem. The local instances are
exactly `completionRCLike` and `InfiniteAdelicGroupPoints.smoothChartedSpace`
at this witness. The real model is the original finite product
`InfiniteAdelicGroupPoints.smoothModel F d`; the target uses the original
`ArchimedeanMatrix F n` with its matrix operator norm convention.

## Actual tangent comparison

`infiniteRealLieAlgebraEquiv` is a real linear equivalence from the actual
identity tangent `GroupLieAlgebra` of the specified infinite adelic manifold
to the existing `ArchimedeanGL.RealLieAlgebra F n`. It differentiates
`infiniteDiffeomorph F n hsmooth` at the identity, uses the continuous linear
equivalence supplied by its smooth inverse, and then applies the inverse of
the original `realLieAlgebraToMatrix`. Thus the tangent identification is
constructed rather than supplied. `infiniteRealLieAlgebraEquiv_apply` states
its exact forward derivative formula. This result asserts a real linear
equivalence; it makes no assertion about Lie brackets.

The helper `groupDirectionalValue_comp_mulHom` proves naturality of the
actual orbit derivative under a smooth group homomorphism from a real charted
group into a real smooth group. Its function is real smooth and complex
valued. The proof identifies the two orbit functions by preservation of
multiplication, then applies the manifold chain rule at the identity using
preservation of one. No smooth group law is required on the source for this
helper.

For a complete real normed algebra, `units_mfderiv_val` identifies the
derivative of the units value chart with the identity map.
`units_mulInvariantVectorField` differentiates left multiplication and proves
that the actual invariant tangent at a unit `g` is `(g : R) * X`. It uses the
value chart, the ambient continuous linear multiplication map, and two chain
rules. Consequently `units_groupDirectionalValue` identifies the right-orbit
derivative of a smooth function with its manifold derivative in direction
`g * X` in the original units atlas.

## Original differential and functions

`infinite_groupDirectionalValue` proves that differentiating
`h ↦ f(infiniteHomeomorph F n h)` at an actual adelic point `g` equals the
original `ArchimedeanGL.smoothDifferential` of `f`, evaluated at
`infiniteHomeomorph F n g`, in the tangent direction obtained by
`infiniteRealLieAlgebraEquiv`. Here `f` belongs to the unchanged original
`ArchimedeanGL.SmoothFunctions F n`. The proof uses the exact original
coefficient-coordinate group equivalence, the proved naturality helper,
the units tangent formula, and the existing
`ArchimedeanGL.smoothDifferential_eq_mfderiv`.

`plotSmoothGeneralLinearEquiv_differential` packages this equality on the
original complex smooth-function spaces:

`E (D_actual X f) = D_original (infiniteRealLieAlgebraEquiv X) (E f)`,

where `E` is the unchanged `plotSmoothGeneralLinearEquiv F n` and `D_actual`
is `InfiniteAdelicGroupPoints.plotSmoothDifferential F GLG hsmooth` on the
existing `GLG.plotSmoothFunctions` carrier. The proof applies subtype and
function extensionality to the preceding pointwise formula and cancels the
original point homeomorphism with its inverse. The existing positive right
pullback action, already compared by `plotSmoothGeneralLinearEquiv_rightAction`,
is retained. In particular this comparison introduces no inverse or minus sign
in differentiation.

`reductiveInfiniteRealLieAlgebraEquiv` specializes to the exact canonical
`reductiveChartedSpace`, using
`isConnectedReductive_generalLinear` and its proved `smoothDimension_spec`.
`plotSmoothGeneralLinearEquiv_reductiveDifferential` compares the resulting
`reductiveRealPlotSmoothDifferential` with the original differential. These
specializations require no supplied dimension or tangent identification and
include `n = 0`.

This unit establishes the first-order differential comparison only. Lie
brackets, enveloping actions, exponential-curve comparison, finite adelic
slice differentiation, growth estimates, quotient measures and cuspidal
Hilbert-space constructions remain separate obligations.
