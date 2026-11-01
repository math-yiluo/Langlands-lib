# Finite central smoothing range and conditional exact reproduction

Worker 94 defines `compactCentralKernels K n`, the complex submodule of
actual compact smooth kernels invariant under conjugation by the whole
standard compact subgroup. For a fixed actual derivative-topology smooth
function, `centralSmoothingMap` restricts the published bilinear smoothing
map to that submodule. Its output is the actual smooth lift of raw
convolution. All number-field universes, natural ranks and compatible
Borel left Haar measures are retained.

The range-containment theorem takes an explicit finite decomposition of
the function into vectors simultaneously in its closed full group orbit
and in specified actual compact types. Smoothing preserves the closed
orbit by the companion invariance helper and the published closed-orbit
containment of smoothing. Centrality preserves each compact type by the
published intertwining theorem. Linearity then places the output in the
finite sum of the corresponding intersections. If those intersections
are finite-dimensional, so is the actual range. The proof never
distributes intersection over a sum of compact types.

`mem_closure_range_centralSmoothingMap` explicitly assumes
`CompactCentralConvolutionApproximationStatement K n`. Every neighborhood
of the original function then contains an actual central convolution.
Pointwise equality identifies the supplied smooth lift with the
published smoothing map, so the function belongs to the closure of the
actual linear range.

`exists_central_reproducingKernel_of_finite_range` also explicitly assumes
finite dimension of that range. A finite-dimensional submodule of the
published Hausdorff topological vector space is closed. Thus closure
membership gives an actual kernel in the domain whose smoothing equals
the original function. This conditional kernel has compact support and
compact conjugation invariance; no positivity, normalization or
prescribed support is asserted for it.

These are internal linear and topological consequences of the published
actual smoothing construction. This unit neither proves central
approximation nor supplies the finite decomposition or finite
compact-type multiplicities. Those hypotheses remain explicit for later
instantiation. It does not prove unconditional reproduction for
automorphic forms or polynomial growth.
