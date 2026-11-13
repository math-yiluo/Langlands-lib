# Comparing the binary diagonal with the full spin kernel

This is an internal comparison API derived from the published binary spin
homomorphism, the scheme-theoretic kernel pullback and fpqc reflection of
group-scheme isomorphisms. It retains the explicit degree-two norm-one
simple-connectedness premise needed to construct the binary lifts.

`BinarySpinLift.diagonalKernel` factors the existing `diagonalSpin` from the
original diagonalizable group scheme μ₂ into the actual kernel of the supplied
spin cover. Its composite with the kernel inclusion is the original diagonal
spin morphism. The factorization is the group-scheme pullback lift, justified by
the published equation `diagonalSpin_comp`.

An isomorphism of this factorization implies monomorphy of `diagonalSpin`.
Every point of the actual kernel then has a preimage under the diagonal spin
morphism by applying the inverse factorization. The published
`diagonalSpin_range` puts that point in the binary-product image, establishing
the other premise of the binary kernel-generation reduction. Conversely,
diagonal monomorphy and full-kernel coverage give equal represented subgroup
functors. Uniqueness of representing group schemes makes the same
factorization an isomorphism.

`SpinKernel.kernelGenerator_of_isIso_diagonalKernel` applies these facts and
the affine binary reduction to any supplied Levi lift pair. Its fpqc
base-change variant first uses the published `isIso_of_baseChange`. The
field-extension variant supplies the three fpqc conditions using
`fieldExtension_fpqc`. Thus a structural comparison over a splitting field
can establish the result over the original field without descending individual
points.

All points and all kernels here are scheme-theoretic, including nonreduced
tests in characteristic two. No restriction on the coefficient algebras is
introduced. The structural isomorphism is a premise, not a theorem of this
module. This module does not prove the unconditional
`SpinKernelGeneratorStatement`.
