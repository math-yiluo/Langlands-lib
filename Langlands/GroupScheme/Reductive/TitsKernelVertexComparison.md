# Simple vertices of the actual anisotropic-kernel subdiagram

Author: Worker 177.

This is an internal consequence of the published actual
`TitsIndexData.KernelComparison` interface, the kernel-index proof, and
`titsIndexStarInvariant`. It works over every field `k : Type u` and keeps
the affine and locally finite type assumptions for both groups. It adds no
local arithmetic or rank-one admissibility assertion.

`zeroStar` restricts the actual full absolute Galois star action to the ambient
simple vertices whose actual root restriction is zero. The published
`titsIndexStarInvariant` proves that the image remains in this subset.

Given `h : d.KernelComparison ι e`, `KernelComparison.vertexEquiv` chooses
the root equivalence in that comparison and restricts it to simple vertices.
The base-membership iff gives a map from every simple vertex of `e` to a
simple vertex of `d` with zero restriction, and gives the inverse on every
such ambient vertex. The inverse laws are those of the chosen root
equivalence. This choice is made only from the supplied actual comparison;
it does not introduce a freely assigned diagram.

`vertexEquiv_cartan` is the comparison's root-pairing equality, restricted to
simple vertices and read in the direction from ambient to kernel.
`vertexEquiv_star` is its full-star equivariance, with subtype equality used
to retain the zero-vertex membership. Both hold for each ordered pair of
vertices or each absolute Galois element, respectively.

`zeroNumbering` transports a supplied kernel numbering to the ambient zero
vertices by composing the inverse vertex equivalence with that numbering.
`zeroNumbering_cartan` transports every entry of any supplied integral kernel
matrix. `zeroNumbering_star` identifies the numbered ambient action with the
actual action on the corresponding kernel vertex. Finally,
`star_trivial_iff` proves that all kernel vertices are fixed by the full
action exactly when all ambient zero vertices are fixed: the two directions
use the equivalence's surjectivity and injectivity and its star comparison.

The root equivalence, pairings, bases and star actions all come from the same
`KernelComparison`. The published `titsAnisotropicKernelIndex` supplies such
a comparison for actual representatives of the derived centralizer, with its
stated hypotheses. These helpers neither assert that this kernel is absolutely
almost simple or simply connected nor classify its components. In particular
they do not supply the local type-A and innerness inputs, division-degree
restrictions, exceptional or trialitarian exclusions, or the unconditional
local rank-one enumeration.
