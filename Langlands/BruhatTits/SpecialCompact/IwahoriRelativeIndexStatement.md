# Relative indices from compatible Iwahori factorizations

Author: Worker 103.

`IwahoriRelativeIndexStatement` is an internal counting statement for arbitrary
groups. It uses the actual multiplication and literal intersections of
`HasIwahoriIntersectionDecomposition`: every element of each of `K`, `J`, and
`H` has a unique ordered factorization in the intersections with `V`, `M`,
and `U`.

The subgroup containments are `H ≤ J ≤ K`. The subgroup `H` is normal inside
`K` and has finite index there, expressed by `H.relIndex K ≠ 0`. The subgroup
`J` need not be normal. An additional subgroup `P` contains `M` and `U` and
is disjoint from `V`. The conclusion is

`[K : J] = [K ∩ V : J ∩ V] * [K ∩ M : J ∩ M] * [K ∩ U : J ∩ U]`.

The right side is written with `J.relIndex (K ⊓ V)` and its `M` and `U`
counterparts. The subgroup containments make these the displayed literal
intersection indices. All indices are natural numbers.

The internal provenance is quotient counting followed by subgroup index
towers. The disjointness condition allows the first factor to be separated
from `P`, while the ordered decomposition gives the remaining `M`, `U`
factorization inside the intersection with `P`. The compatible factorization
of the common normal subgroup gives the index product in the finite quotient.
Index towers then cancel the common subgroup and remove the normality
requirement on `J`.

In the intended application, `V` is the opposite unipotent radical, `P` is the
actual parabolic, and `M` and `U` are its Levi and radical. The statement
constructs none of these subgroups and proves no existence of a simultaneous
compact open normal basis. It does not assert that an arbitrary ordered triple
factorization alone suffices: the subgroup `P`, its containments, the
disjointness condition, and the compatible common normal subgroup are
explicit hypotheses.
