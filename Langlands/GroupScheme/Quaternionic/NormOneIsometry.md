# The reduced-norm-one subgroup of an actual isometry group

Author: Worker 177.

This internal construction restricts the published actual reduced norm of
`Matrix n n D` to the published isometry group of a Tits quadratic form.
Here `D` is a finite-dimensional central division algebra over an arbitrary
field `K`, its first-kind involution is supplied, and the finite matrix
index type is nonempty. The form has no regularity hypothesis.

`normOneIsometryGroup q` is the actual kernel of this restricted character.
`normOneIsometryGroupι` includes it in the isometry group, and
`normOneIsometryAmbientι` is the composite inclusion in the matrix-algebra
unit group. Both inclusions are closed; the ambient inclusion is a
monomorphism. Closedness follows from the kernel construction and the
separatedness of the multiplicative group, followed by composition with
the published closed isometry inclusion.

The first range criterion says that a point of the isometry group belongs
to this kernel precisely when its ambient reduced norm is one. The second
says that an ambient point belongs precisely when it is an isometry and
has reduced norm one. Both statements quantify over every test scheme.
The last criterion writes these two conditions in the published tensor
coordinates: for any representative `Q` of the quotient-valued quadratic
form, the defect `X * (1 ⊗ Q) * transposeInvolution(X) - 1 ⊗ Q`
belongs to the base change of the quadratic kernel, and the actual
reduced norm of the tensor unit `X` is one. This includes nonreduced
test schemes and is independent of the representative.

The provenance is internal specialization of the published kernel range
criterion, isometry-cut range criterion, and actual reduced-norm point
comparison. The proof follows the same kernel-intersection argument as
the published symplectic ambient inclusion. No assertion of smoothness,
connectedness, reductivity, or a type-B presentation is made. In
particular, this construction is defined even for forms whose full
isometry group is not smooth.
