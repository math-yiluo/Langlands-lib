# Actual affine pinned models from coherent global root frames

This internal consumer interface records frames of actual root modules on every
affine test of an arbitrary base and constructs the corresponding actual affine
pinned models. It retains a supplied global full coordinate root datum and its
chosen base.

`AffineRootFrames` is supplied data: for each map from the spectrum of an actual
commutative ring to the original base, and each root, it is a linear equivalence
from that same ring to the actual exponent-weight module of the normalized
pulled-back group. `point` projects the frame vector at one to an actual
dual-number point of the original group. `IsCoherent` is the equation identifying
coefficient extension of this point with the frame on the direct affine test.

`pinnedAffineModelOfFrames` uses a reductive group, a closed split fibrewise
maximal torus, a full global coordinate root datum, supplied frames and a base.
It takes an actual affine pullback of the original group; the torus inclusion
uses the canonical split-torus pullback isomorphism. Closedness, maximality and
actual field realization are transported from the original data. The supplied
root frames give all the required root lines and the simple pinning vectors.

Construction of these frames from actual root line bundles and the Picard
hypothesis is a separate prerequisite. No freeness or Picard consequence is
asserted by the frame interface itself.
