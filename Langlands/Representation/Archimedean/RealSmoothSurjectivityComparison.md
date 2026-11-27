# Detecting surjectivity through a second real smooth representation

Let \(J\) be a continuous linear map between genuine smooth carriers for
real general linear group actions, equivariant under the compact group. The
source Banach action is jointly continuous and the target action is on a
complex normed space. If \(J\) is injective on the source's compact-finite
vectors, `injective_of_injective_smoothKFinite` shows it is injective on the
entire genuine smooth carrier. Its kernel is closed and compact invariant.
The compact-finite part of the kernel is dense in the kernel by the
orthogonal polynomial averaging theorem for closed subspaces. Injectivity
makes that part zero, and the Hausdorff word topology gives a zero kernel.

`RealSmoothSurjectivityComparisonStatement` takes an additional map \(Q\)
with dense range in the source of \(J\). If the range of \(J\circ Q\) is
closed in the second carrier, continuity of \(J\) places every \(J(y)\) in
that range. Injectivity then lifts \(y\) through \(Q\). In a principal-series
quotient application, the quotient's compact-finite image is dense, and the
comparison applies once there is a continuous compact-equivariant extension
of an algebraic embedding and the composite has closed range.
