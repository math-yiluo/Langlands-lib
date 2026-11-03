# Exact kernels from fixed pure tensors

Worker 1228.

This internal construction turns an explicitly supplied subgroup-fixed tensor
into an actual finite representation whose represented kernel is the given
normal affine subgroup. It uses the published tensor representation and the
normal fixed-space restriction.

The first elementary lemma works over any commutative ring. Suppose each of two
vectors has a coordinate equal to one. If a transformed pure tensor equals the
original tensor, the product of the two corresponding transformed coordinates
is one. Thus the first transformed coordinate is a unit. The remaining tensor
coordinates show that the first transformed vector is that unit times the
original vector. This argument works for arbitrary rings, including those with
nilpotents.

The scheme version computes the actual tensor representation on every test
scheme. If the tensor is fixed, its first factor's coordinate line is preserved.
Assume this line's stabilizer is contained in the prescribed subgroup, and
assume the tensor itself is fixed by the subgroup on all tests. Normality then
makes the full subgroup-fixed space an actual subrepresentation. Its kernel
fixes the supplied tensor, hence preserves the line and belongs to the subgroup.
The converse follows from the trivial subgroup action on the full fixed space.
`KernelRepresentation` records this equality of actual represented-kernel range
and subgroup range, and `kernelRepresentationOfFixedTensor` chooses that data.

The field universe is arbitrary. Affineness of both group schemes is assumed;
subgroup smoothness, connectedness and characteristic restrictions are absent.
The supplied fixed tensor is an explicit hypothesis. This file does not prove
that every normal closed subgroup admits such a tensor and does not construct
the desired affine quotient. The proof is an internal matrix calculation and
application of the actual tensor and normal fixed-space constructions; it uses
no additional external mathematical premise.
