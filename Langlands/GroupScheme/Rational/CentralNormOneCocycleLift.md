# Lifting cocycles through norm-one torsion

`Cocycle.LiftsAfterFiniteGaloisRefinement` asserts that a natural
cocycle over a field `F` lifts through a group-scheme homomorphism
on a finite Galois field cover extending the given coefficient cover.
The projected lift equals the refinement of the whole natural cocycle.

Suppose the homomorphism is a central isogeny whose kernel is
identified with the `n`-torsion in the Weil norm kernel for a finite
field extension `B/F`. The corresponding affine kernel coordinates
are actual tensor units with norm one and `n`-th power one. On a
Galois coefficient cover `L/F`, start with a choice of pointwise lifts
of the Galois values of the cocycle `ξ` over `L`. If the inflation of
their central tensor defect has a primitive in this subgroup on a
finite Galois refinement, the inverse point equivalence gives a
kernel-valued primitive on the same cover. Equivariance and naturality
of the tensor point map verify its differential. The central lifting
criterion then gives a lift of the natural cocycle.

For a compatible tower of number fields `F ⊆ B ⊆ L` with `L/F`
finite Galois and `n` positive, assume `ξ` is everywhere locally
trivial and the pointwise lifts over `L` are supplied. The tensor-unit
obstruction of these lifts vanishes, and a finite Galois refinement
using tensor radicals gives an `n`-torsion tensor-unit primitive for
the inflation of their defect. To apply the lifting criterion, a
separate argument must produce a norm-one torsion primitive. The
norm correction in `tensorNormOnePrimitiveAfterRefinement_of_normPower`
uses a Kummer radical for the norm of the torsion primitive and
requires its radicand to be a norm from `B` times an `n`-th power in
`F`.
