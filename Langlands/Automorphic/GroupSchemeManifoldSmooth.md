# Ordinary manifold smoothness on the existing actual adelic spaces

This internal construction identifies the existing all-family smooth-function
condition with ordinary smoothness for the specified infinite adelic manifold.
It applies to a number field F in an arbitrary universe, an affine group scheme
G over F, a natural number d and `SmoothOfRelativeDimension d G.X.hom`.
The atlas is exactly `InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth`;
the real model is `smoothModel F d`, using the specified compatible
`completionRCLike` structures. All smoothness is real C∞.

`InfiniteAdelicGroupPoints.isPlotSmooth_iff_contMDiff` states that a complex
function on the original infinite adelic scheme points satisfies the existing
`G.IsPlotSmooth` predicate, using `ringEquiv_mixedSpace`, exactly when it is
ordinary smooth for this atlas. The forward proof tests the identity family
on the constructed actual manifold. Its model and carrier lie in the coefficient
universe, so this test is included in the existing predicate's quantifiers.
The general coordinate-family criterion proves that the identity is an allowed
test. Conversely, every tested family is smooth for this atlas by that same
criterion; composition proves the required smoothness of the tested function.
The predicate continues to quantify over arbitrary charted parameter spaces,
without imposing a manifold or completeness hypothesis on them.

`manifoldSmoothFunctions` is the ordinary smooth-function complex submodule
on the original point carrier. Closure follows from smoothness of the zero
function, addition and fixed complex scalar multiplication. The theorem
`plotSmoothFunctions_eq_manifoldSmoothFunctions` proves literal equality with
the existing plot-smooth submodule by the preceding membership equivalence.
`manifoldSmoothFunctions_eq` proves equality for any two supplied relative
dimensions and witnesses by identifying both submodules with the same original
plot-smooth submodule. This is an equality of spaces of functions and does not
identify independently chosen charted-space structures.

`reductive_isPlotSmooth_iff_contMDiff` specializes the equivalence to the exact
`reductiveChartedSpace` atlas and its derived dimension using the published
connected-reductive dimension adapter. Its algebraic input is the original
`IsConnectedReductive` predicate; no dimension or analytic smoothness premise
is added. The existing affine-group setting is retained.

In `Langlands.Automorphic.GroupSchemeFunctions`,
`mem_infinitePlotSmoothSubrepresentation_iff_contMDiff` says that the existing
infinite-smooth subrepresentation consists exactly of continuous
rational-invariant functions whose actual infinite slice at every finite point
is ordinary smooth for the specified atlas. It applies the preceding equivalence
to every slice. The slice is the existing restriction through
`AdelicGroupPoints.pair`, with its original ambient continuous function.

`mem_plotSmoothSubrepresentation_iff_contMDiff` retains, in addition, the original
`finiteLocallyConstantSubrepresentation` condition, which requires local constancy
in each finite slice. The theorem
`mem_finitePlotSmoothRationalSubrepresentation_iff_contMDiff` instead retains the
original `finiteSmoothSubrepresentation` condition, which requires a common open
finite stabilizer. Both follow by taking the defining intersection and applying
the infinite-slice equivalence. Neither condition is replaced by the other.
`reductive_mem_infinitePlotSmoothSubrepresentation_iff_contMDiff` gives the
infinite-slice criterion for the canonical connected-reductive atlas.

The function carriers, inclusions and positive full adelic right actions are the
existing ones throughout: this unit changes no subrepresentation or action.
Consequently it interprets the existing spaces through the actual manifold
without introducing a second adelic function-space construction.

The provenance is internal: the specified manifold's proved coordinate-family
criterion, the existing all-family predicate and the original slice-space
definitions suffice for every result. No new external assertion is transcribed.
This unit establishes the ordinary manifold interpretation of the smooth
conditions. Differential moderate-growth estimates, quotient measures, reduction
theory, finite volume and cuspidal L2 realizations remain separate obligations.
