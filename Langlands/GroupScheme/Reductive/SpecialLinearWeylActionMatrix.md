# Field matrices for the kernel of the full based-root projection

This internal construction starts with a split pinning on an affine group
scheme over an arbitrary field, a torus-compatible automorphism, and a supplied
actual adjoint quotient. Its hypothesis is identity of the **full**
`basedRootDatumProjection`, as an automorphism of both integral lattices.

`characterAut_mem_weylImage_of_basedProjection_eq_one` uses the published
kernel theorem for that projection. The contravariant geometric root-datum
equivalence acts on characters by precomposition with the torus map. Its weight
automorphism is therefore the inverse of `characterAut`. The published
abstract-to-actual Weyl image inclusion, followed by inversion in the image
subgroup, puts the actual torus automorphism in the Weyl image.

`adjointPointOfBasedProjectionIdentity` chooses the base point supplied by
`SplitPinning.exists_adjointPoint_of_weylImage`, and its specification identifies
the evaluated inner action with the original group-scheme automorphism.

With any supplied special-linear presentation,
`exists_matrix_of_basedProjection_eq_one` applies
`SpecialLinearInnerForm.exists_matrix_for_adjoint_basePoint`. The resulting
single invertible matrix over the original field gives conjugation on all
test schemes, with coefficients pulled back through `scalarMap`.

The provenance is internal and derived from the published full based projection,
Weyl image comparison and pinned Weyl innerness, and the adjoint-point matrix
bridge. This unit does not identify the full projection from its permutation
of simple roots and does not classify nonidentity diagram actions. It makes
no restriction on characteristic or on the finite coordinate index type.
