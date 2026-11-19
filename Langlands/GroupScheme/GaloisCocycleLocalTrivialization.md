# Galois values of a trivialization over an extended base field

Let `L/F` be normal and let `K/F` be a field extension. Suppose a
natural cocycle on the cover `Spec L → Spec F` becomes trivial on its
pullback to `K`. For any field `M` containing `K` and `L` compatibly
with `F`, the theorem
`GaloisCocycle.exists_galois_coboundary_of_baseChange_isTrivial`
gives a point `a` of the original group over `M`. For every
`K`-automorphism of `M`, the cocycle value at its restriction to `L`
extends to the coboundary of `a` under that automorphism.

The compatible inclusions give `GaloisCocycle.pullbackCoverPoint`,
a point of the pullback cover over `M`. This point and its translate by a `K`-automorphism have the same
projection to `Spec K`. The relative trivialization identity therefore
applies to the pair. Its projection to the original cover is the field
refinement and its translate by the restricted automorphism. Naturality
identifies the resulting cocycle value with the extended Galois value.

This is an internal comparison on the actual pullback cover. It can
be used with a completion as the new base field and an extension of
that completion as the coefficient field.
