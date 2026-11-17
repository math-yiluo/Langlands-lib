# The adjoint torus of a relative Borel is a finite etale Weil torus

`relativeBorelAdjointTorusWeilPresentation` proves the unchanged
`RelativeBorelAdjointTorusWeilPresentationStatement` in every universe,
without additional hypotheses. For any commutative ring, supplied reductive
ambient group, relative Borel and relative maximal torus in that Borel,
every supplied full fppf quotient of the torus by the inverse image of the
ambient full centre is actually isomorphic to the Weil multiplicative group
for a finite projective etale algebra over the original ring.

The implemented proof applies the supplied-data construction
`SuppliedBorelAtlas.ofData` to the given ambient group, Borel and torus.
`SuppliedBorelAtlas.hasEtalePermutationAtlas` provides the permutation atlas
for the actual given quotient. Its local construction retains the supplied
torus and Borel, realizes the full root datum, constructs exact simple-root
quotient maps, derives the fibre permutations from the actual pair-preserving
maps, and extends those same permutations to open overlap neighbourhoods.

The final line applies `permutationAtlasWeilPresentation` to this actual
atlas. That theorem descends the finite simple-root coordinate coefficients,
constructs a finite projective etale algebra over the original ring, and
glues actual group-scheme isomorphisms with its Weil multiplicative group.
The result concerns the supplied quotient, with no affineness assumption on
it, and retains the full central kernel, including non-smooth factors.
Varying ranks and empty simple-root supports are permitted; the coefficient
algebra may be the zero ring. This is a derived proof through the imported
atlas and descent constructions, rather than a new literature transcription.
