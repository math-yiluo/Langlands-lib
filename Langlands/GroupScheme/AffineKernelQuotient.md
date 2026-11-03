# Smooth affine quotients from prescribed affine kernels

`AffineKernelQuotientStatement.{u}` asserts that an actual homomorphism from a
smooth affine group over any field `k : Type u` into an affine locally finite
type group has a smooth affine fppf quotient by its full scheme-theoretic
kernel. `affineKernelQuotient` proves this statement using the actual schematic
image group and the original projection. No smoothness premise is placed on
the kernel.

This helper is derived from `AffineHomImage`, `DominantHomFaithfullyFlat` and the existing
all-test kernel correspondence `mem_range_kernelι_iff`. Restricting the codomain
to the image leaves the full kernel range unchanged: on any test scheme a point
maps to one in the image precisely when its image in the original target is
one, by cancellation of the monomorphic image inclusion. The image projection
is flat, surjective and locally of finite presentation by
`AffineHomImage.projection_geometry`. Together these facts give exactly the
published `RelativeRoot.IsFppfQuotient` predicate.

`exists_quotient_of_affine_kernel` permits replacing that full kernel by any
specified represented subgroup having the same all-test range. Its conclusion
is the desired smooth affine quotient conclusion, with no additional condition
on the represented subgroup.

`NormalSubgroupAffineKernelStatement` isolates the remaining construction
input: each normal closed subgroup of a smooth affine group is the full kernel
of an actual homomorphism into some affine locally finite type group over the
same field. This proposition is defined here and remains unproved here.
`normalSubgroupQuotient_of_affineKernel` proves that this construction input
implies the unchanged `NormalSubgroupQuotientStatement.{u}`, preserving all
field and universe quantifiers. This conditional reduction does not prove the
normal-subgroup quotient theorem without that input.
