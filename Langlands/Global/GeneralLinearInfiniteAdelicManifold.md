# Original general-linear manifold comparison

This internal construction compares the specified infinite adelic manifold on
actual general-linear scheme points with the existing mixed-coordinate
matrix-units manifold. It uses the existing point and coordinate maps throughout.
Let F be a number field in an arbitrary universe and n any natural number,
including zero. Write G for `GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)`.
The first three results take `SmoothOfRelativeDimension d G.X.hom` for a natural
number d. Affineness is supplied by the existing general-linear group theorem.

The source atlas is exactly
`InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth`, with real model
`InfiniteAdelicGroupPoints.smoothModel F d`. The completion normed-field
structures are exactly the compatible `completionRCLike` structures used by
that construction. The target is the original `ArchimedeanGL F n` manifold:
units in `ArchimedeanMatrix F n`, the matrix algebra over the mixed real/complex
space with the existing row-sum norm convention. All smoothness is real C∞.

`contMDiff_infinite_iff_matrixCoordinates` tests an incoming family p from an
arbitrary charted space with a real model with corners. It states that p is
smooth for the specified source atlas exactly when
`archimedeanGLCoordinates F n ∘ infiniteHomeomorph F n ∘ p` is smooth into the
original matrix-units manifold. No manifold assumption on the parameter space
is added; its model and carrier universes are independent of the coefficient
universe. The proof composes the general infinite adelic all-regular-function
criterion with the existing general-linear coordinate criterion.

`infiniteDiffeomorph` bundles this comparison. Its underlying equivalence is
`GeneralLinear.coefficientCoordinatesEquiv` for
`InfiniteAdeleRing.ringEquiv_mixedSpace F`. The equality
`infiniteDiffeomorph_toEquiv` identifies it definitionally with the composite
of the original `infiniteHomeomorph` and `archimedeanGLCoordinates`.
Forward smoothness follows by applying the incoming criterion to the identity
family on the source. For the inverse, apply the same criterion to the inverse
coefficient-coordinate equivalence. Its coordinate expression is the identity,
using the existing equivalence inverse law, and hence is smooth.

`contMDiff_iff_mem_smoothFunctions` states that a complex function f on the actual
infinite adelic scheme points is smooth for this atlas exactly when
`x ↦ f (infiniteHomeomorph.symm x)` belongs to the original
`ArchimedeanGL.smoothFunctions F n`. That existing submodule is a space of
functions on completion-based matrix points whose mixed-coordinate expressions
are smooth. The result follows by composition with the inverse diffeomorphism;
its function expression agrees definitionally with that original membership
condition.

`reductiveInfiniteDiffeomorph` uses the published
`isConnectedReductive_generalLinear` theorem and the dimension derived by the
connected-reductive adapter. Its source is exactly `reductiveChartedSpace`,
with the corresponding selected dimension. It thus gives the same comparison
without a separate dimension or analytic hypothesis, and without a positive-rank
restriction.

The provenance is internal: the actual point equivalence, coefficient
equivalence, existing general-linear coordinate test and original smooth-function
definition are composed with the constructed infinite adelic atlas and the
published connected-reductive theorem. No new external assertion is transcribed.
The construction establishes a manifold and function-space comparison; it makes
no differential-growth, quotient-measure, reduction-theory, finite-volume or
cuspidal Hilbert-space assertion.
