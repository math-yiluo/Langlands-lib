# Actual representations with a prescribed unipotent normal kernel

This internal construction combines the published actual Chevalley coordinate
line stabilizer with normal fixed-space coordinates and unipotent stable-line
fixedness. No further structural theorem is assumed.

`KernelCoordinates i` contains a finite coordinate dimension, an actual
representation of the ambient group on these coordinates, and equality of
its full scheme-theoretic kernel range with the subgroup range of `i`.

For an affine group locally of finite type over an arbitrary field and a
closed unipotent normal subgroup, `unipotentKernelCoordinates` constructs this
data as follows. The actual Chevalley theorem provides a coordinate line whose
unit-scalar stabilizer is exactly the subgroup on every relative scheme test.
Unipotence makes its coordinate unit vector fixed by the subgroup. Split
coordinates for the subgroup's fixed subspace give an actual representation:
normality and the affine coefficient argument prove all-test stability.

The subgroup acts trivially on these coordinates, which proves one kernel
inclusion. Conversely, a point in the kernel fixes every vector in the image
of the coordinate projection. The original coordinate unit vector lies in
that image, so the point fixes it and belongs to the original line stabilizer,
using the scalar unit one. Both inclusions hold on all scheme tests, giving
the stated equality of subgroup functors.

This constructs the ambient representation with its exact kernel. Descent to
a faithful representation of a supplied fpqc quotient, and affineness of the
quotient, remain separate obligations.
