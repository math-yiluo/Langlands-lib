# Normalized bilinear forms on restricted tensor products

This internal construction for Task 7294 supplies the algebraic finite-adelic
pairing assembly. It works over an arbitrary field and uses the actual
restricted tensor product already constructed in the Library.

At a finite stage the local bilinear forms are tensored using Mathlib's
indexed tensor map for bilinear maps, and the resulting scalar tensor
is evaluated by multiplication. The formula on two pure tensors is
the product of the local pairing values.

Assume that the form evaluated on the reference vector twice is one
outside the exceptional set. Extending both inputs to a larger finite
stage then preserves the finite-stage form: the new factors contribute
one. Mathlib's binary direct-limit lift descends these compatible
values to the actual restricted tensor product. Common-stage
direct-limit induction proves linearity in both arguments.

If every local form is nonzero, suitable vectors in the exceptional
stage give a product of nonzero values. For an empty exceptional
stage this product is one. This proves that the descended form is
nonzero.

Finally, two families of local linear operators that preserve the
reference vectors almost everywhere induce maps on the restricted
tensor product. If the local forms are invariant under these two
operators, the descended form is invariant under the induced maps.
Enlarge the common stage to contain both finite bounds for reference
preservation, apply the componentwise finite-stage action formula,
and use the product formula for the stage pairing.

No local form existence, normalization, or automorphic factorization
is asserted here. The provenance is internal algebraic infrastructure
for the host task; the paired Lean implements the construction and
its stated properties from the existing actual direct-limit API.
