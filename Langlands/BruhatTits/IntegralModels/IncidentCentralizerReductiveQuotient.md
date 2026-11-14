# Full kernels of incident centralizer composites

This internal deduction combines the actual integral centralizer comparison
with the published kernel transport under a change of source coordinates.

For a compatible morphism of relative component models and a split integral
torus, `centralizerTargetReductiveQuotientMap` is the original source residue
centralizer inclusion followed by the ambient special-fibre morphism and the
target radical projection. It is a homomorphism of the actual group schemes.

Over maximal-unramified integers, suppose the ambient neutral integral-point
images are the common zero subgroup intersected with the fixers of two nonempty
apartment subsets. The integral centralizer comparison supplies an isomorphism
of the actual integral centralizer models. Its residue base change commutes
with the ambient map. Postcomposing that equality with the radical projection
and applying `kernelCoordinateIso` gives
`centralizerTargetReductiveQuotientKernelIso`, an isomorphism between the full
original source-composite kernel and the target same-model centralizer kernel.

If the supplied quotient is a reductive radical quotient, the latter kernel
is smooth by the smooth restriction theorem for full whole-torus centralizers.
Smoothness transports through the isomorphism over the residue base, proving
`centralizerTargetReductiveQuotientMap_smooth_kernel`.

No incidence or boundedness premise is needed for this centralizer factor.
The conclusion uses the full scheme-theoretic kernel, including infinitesimal
tests. Smoothness of the ambient incident map is not assumed. The compatible
root and centralizer product charts needed for the full ambient composite
kernel remain a separate obligation of the common-torus proof.
