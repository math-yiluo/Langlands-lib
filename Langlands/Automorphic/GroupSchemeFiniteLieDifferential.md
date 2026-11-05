# Conditional Lie action on the original finite-smooth adelic carrier

For an affine group scheme over any number field, with a specified smooth
relative dimension, `realFinitePlotSmoothLieAction` bundles the unchanged
`realFinitePlotSmoothDifferential` into a real Lie homomorphism whose values
are complex-linear endomorphisms of the original
`FinitePlotSmoothRationalFunctions` space.

The additive group needed for the endomorphism commutator is supplied by
`Module.addCommMonoidToAddCommGroup ℂ` on the unchanged finite-smooth module;
its negation is scalar multiplication by `-1`. This adds no hypothesis.

The selected manifold is exactly the existing `smoothChartedSpace` with its
constructed `smoothLieGroup` structure. The source is its actual identity
tangent Lie algebra; the target bracket is the endomorphism commutator.
The generic scalar identity `smoothVectorFieldCommutator` for that manifold
remains an explicit hypothesis.

The implemented proof extracts each original infinite slice, uses the existing
slice differentiation formula, and applies the bracket law of
`realPlotSmoothLieAction`. Faithfulness of those slices then gives equality
of finite-smooth functions. This adds no choice of stabilizer or replacement
action: the underlying linear map and its already proved preservation of every
specified finite subgroup remain unchanged.

The generic scalar commutator is still unproved. This conditional construction
does not establish an unconditional Lie or enveloping action, an exponential
comparison, derivative growth, quotient measures, reduction, finite volume or
an L2 realization.
