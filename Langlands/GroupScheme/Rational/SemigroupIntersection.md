# Exact intersections of actual semigroup subgroups

Let `k : Type u` be any field, let `G/k` be a smooth affine group scheme,
and let a split torus `S` act on `G` by the existing
`AutomorphicAction S.toGrp G`. Neither connectedness of `G` nor reductivity
is assumed. Let `A` and `B` be additive subsemigroups of the actual character
lattice of `S`, and suppose `0 ∉ A`. The second semigroup is arbitrary; it
may contain zero.

`semigroupSubgroup_inf_eq` proves the equality of intrinsic subgroup
functors

`semigroupSubgroup b A ⊓ semigroupSubgroup b B
  = semigroupSubgroup b (A ⊓ B)`.

The intersection on the left is the pointwise intersection. Thus the
equality holds on every scheme over `k`, including nonreduced tests.
The semigroup intersection on the right selects exactly the characters
lying in both semigroups. No hypothesis about rational-point density or
an intersection chosen only on field-valued points occurs.

`semigroupIntersectionPointsEquiv` is the multiplicative equivalence
between the point group of the left-hand intersection and that of the
right-hand subgroup on any supplied scheme test. It is induced by the
proved equality, and `semigroupIntersectionPointsEquiv_val` says that it
preserves the underlying point of the original `G`.

The implemented proof realizes the `B` subgroup by a smooth connected
closed inclusion `j : U → G` and gives `U` the induced `S` action `c`.
Equivariance of `j` and the exact Lie-image clause of semigroup realization
show that the entire action support of `U` lies in `B`. Consequently `A`
and `A ⊓ B` select the same ambient weights on `U`, and the existing
weight-support congruence theorem identifies their semigroup subgroups
inside `U`.

The existing zero-excluded inverse-image theorem identifies the full
inverse image of `semigroupSubgroup b A` under `j` with
`semigroupSubgroup c A`. Its geometric and coordinate prerequisites are
discharged by the published `semigroupRealization` and the containment
part of `CoordinateWeights.coordinateSemigroupComparison`. In particular,
this proof does not assume connectedness of that inverse image.
Mapping it back into `G` gives the pointwise intersection with the range
of `j`, which is the `B` subgroup. Replacing `A` internally by `A ⊓ B`,
then applying equivariant closed-inclusion image transport, gives the
claimed equality.

The provenance is internal: every step is a deduction from the existing
semigroup realization, zero-excluded intersection, coordinate-support
comparison and equivariant transport theorems. This unit adds no assertion
from external literature. It proves no valuation axiom or building
comparison.
