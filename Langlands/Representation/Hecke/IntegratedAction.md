# Integrated action on a smooth representation

This internal construction defines the actual action integral
`integratedAction μ ρ hρ f v` as the algebraic finite-fiber integral of
`g ↦ f(g) • ρ(g)v`. It uses the positive representation convention. The test
function is an actual `HarmonicAnalysis.SchwartzBruhat G`, with the published
`Hecke.TestFunction` API.

The group and vector space occupy independent universes. The group is a
topological group equipped with a measurable structure containing its open sets;
the measure is finite on compact sets. The vector space is only an additive
commutative group and complex module. Smoothness makes every orbit map locally
constant. Compact support therefore makes the action integrand a finite-image
simple function with finite-measure support. No norm, topology, completeness or
finite-dimensionality on the vector space is assumed.

Any finite measurable indicator presentation of the weighted orbit map computes
the action by its weighted vector sum. Only nonzero values require finite
measure. Applying this formula to two presentations proves that different
support cutoffs, partitions or subgroup-coset refinements give the same result.
The definition itself chooses no support cutoff or subgroup.

The bilinear map is constructed from the established integrand linearity and the
finite-fiber integral's additivity and complex homogeneity. Intertwiner
compatibility follows from the integrand identity and commutation of the
algebraic integral with arbitrary linear maps. Every algebraic linear functional
evaluates this action as the scalar Bochner integral
`∫ g, f(g) * L(ρ(g)v) ∂μ`. This follows by the same linear-map compatibility and
the complex scalar comparison theorem.

The motivating construction is the natural Hecke action recalled in Flath,
*Decomposition of representations into tensor products*, section 1, printed
page 179 (registered source `flath-1979-tensor-products`). The present finite-fiber
implementation and its proofs are internal derived content. The convolution law is proved in the accompanying
`IntegratedConvolution` module. Normalized projections and corner modules remain
subsequent construction units. The algebraic integral and action integrand are
imported from the published Library.
