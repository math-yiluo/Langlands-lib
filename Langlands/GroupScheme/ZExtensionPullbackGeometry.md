# Geometry of the actual z-extension pullback

These internal consequences of `ZExtensionPullback` supply the geometric
interfaces needed to apply reductivity and simply connected derived-group
ascent to the fiber product in Kaletha–Prasad, Lemma 11.4.3. They follow
from the published definitions of actual kernels, the all-test center,
and affine morphisms; they add no hypothesis to the supplied z-extensions.

`representsKernel` and `kernelIso` identify the product of the two original
kernel groups with the actual kernel of the projection to `G`, respecting
its inclusion. The inclusion is closed because that actual kernel is closed
in a group scheme over a field. It is central because both coordinates
are central; the proof tests equality after the two pullback projections.

The first projection is flat, surjective and locally of finite presentation
by base change from the target extension. Its full kernel is central:
its first coordinate is the identity and its second coordinate factors
through the supplied central kernel. The kernel of the projection to `G`
is central by the earlier full-kernel equality.

The fiber product is affine. Both groups in the target extension are affine,
so its quotient map is affine; base change gives affineness of the first
projection, and composition with the affine structure map of the supplied
source extension finishes the proof.
