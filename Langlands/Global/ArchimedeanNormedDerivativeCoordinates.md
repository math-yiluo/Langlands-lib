# Normed coordinates for the actual derivative topology

This internal helper refines the published genuine enveloping-derivative
coordinates by restricting each coordinate to every compact subset of the
actual infinite-adelic general linear group. The index is the product of the
actual complex enveloping algebra and the type of compact subsets. Each
coordinate space of continuous functions has its supremum norm; empty compact
subsets are allowed. All number-field universes and ranks, including zero, are
retained.

`tendsto_normedDerivativeCoordinates_iff` proves that these coordinates induce
exactly the published derivative topology. Singleton compact restrictions
detect equality, giving `isEmbedding_normedDerivativeCoordinates`.
`contDiffOn_scalar_of_normedDerivativeCoordinates` applies the real
Hahn–Banach and finite-product scalarization helper to a continuous complex
linear functional, regarded as a real linear map into the finite-dimensional
real space of complex numbers.

The construction is internally derived from `ArchimedeanSmoothTopology` and
the generic compact-restriction and scalarization helpers. It introduces no
replacement topology or action and does not yet prove that the actual orbit
coordinates are smooth.
