# Conditional Lie bundling of the actual infinite adelic differential

This internal construction retains the original infinite adelic plot-smooth
function space and the actual tangent differential constructed in
`GroupSchemeDifferential`. It explicitly assumes the still unproved generic
scalar commutator `smoothVectorFieldCommutator` for the specified manifold.

For an affine group scheme `G` over any number field `F` and a proof that its
structure morphism is smooth of relative dimension `d`,
`realPlotSmoothLieAction` bundles `realPlotSmoothDifferential` as a real Lie
homomorphism into complex-linear endomorphisms of the original
`G.plotSmoothFunctions` on the infinite adele ring. The model, charted space
and Lie-group instances are precisely `smoothModel`, `smoothChartedSpace`
and `smoothLieGroup`. Mathlib's tangent Lie algebra uses the bracket of actual
left-invariant vector fields. The endomorphism bracket is composition in the
order `D_X D_Y - D_Y D_X`.

The implemented proof applies
`groupDirectionalValue_commutator_of_vectorFieldCommutator` to each original
smooth function and each actual adelic point. The existing equivalence between
the original all-family plot-smooth predicate and manifold smoothness supplies
its smoothness hypothesis. Thus the underlying linear map is unchanged; no
abstract differential or tangent identification is supplied in place of the
constructed one.

The generic prerequisite remains explicit and is not proved here. This
conditional construction does not establish an unconditional Lie or enveloping
action, exponential curves, derivative growth, quotient measure, reduction,
finite volume or a cuspidal Hilbert-space realization.
