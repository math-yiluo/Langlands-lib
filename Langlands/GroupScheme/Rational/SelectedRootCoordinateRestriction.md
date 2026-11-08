# Selected-root coordinates detect smaller semigroup subgroups

This internal construction works over a field `k : Type u`, at arbitrary
universe `u`. The ambient group scheme `G/k` is affine. Its theorems also
require `G` to be smooth. All subgroup functors are the existing intrinsic
functors, and all conclusions hold on every scheme over `k`, including
nonreduced tests.

Let `i : T.toGrp → G` be a monomorphic homomorphism from a split torus.
Retain `HasOppositeFactorPairs i`. Let `A` and `B` be additive subsemigroups of
the actual character lattice of `T`, with `0 ∉ A` and `B ≤ A`. Let an
injective list `a : Fin n → characterLattice T` enumerate exactly
`semigroupIndivisibleRoots i A`. These are indivisible roots within the
roots selected by `A`, as defined in `SelectedRootSemigroupProduct`.
The smaller semigroup `B` need not contain any of the `a r`.

`rootPointsProductInSemigroup i a B V` takes a tuple whose `r`th entry
belongs to the intersection of the actual root functor `subgroup i (a r)`
and the actual semigroup functor `semigroupSubgroup (conjugation i) B`.
It multiplies the underlying points in the order of `Fin n`, with value
in the original `G(V)`. This definition itself requires neither smoothness,
splitness, monomorphy, opposite pairs, nor the semigroup containment.

The three theorems retain the hypotheses above:

- `exists_rootPointsProduct_in_semigroup_of_mem` gives ordinary `A` root
  coordinates for a point of the `B` subgroup, with every individual
  coordinate still in the `B` subgroup.
- `rootPointsProduct_mem_semigroup_iff` says that the ordered product of an
  arbitrary tuple of `A` root points lies in the `B` subgroup if and only
  if every coordinate lies in it.
- `mem_semigroupSubgroup_iff_existsUnique_rootPointsProductInSemigroup`
  says that a point of `G(V)` lies in the `B` subgroup if and only if it has
  unique coordinates in the intersections used by
  `rootPointsProductInSemigroup`.

The empty enumeration is included: its product is the identity. Coordinate
uniqueness is equality of intrinsic point subtypes and does not depend on
chosen representatives.

For existence, the implemented proof realizes the `B` subgroup as a smooth
connected closed group `U → G`. Since `0 ∉ B`, this group is unipotent.
The induced `T` action on `U` has support exactly
`relativeRoots i ∩ B`, contained in `relativeRoots i ∩ A`. The selected
`A` ray blocks cover the latter set and satisfy pairwise disjointness and
cross-exclusion. The unipotent ordered-product theorem, followed by
`HasOrderedSemigroupProducts.for_larger_support`, gives an ordered
factorization of `U` using those same ray blocks, including empty factors.

Each factor maps into the ambient upper root functor by equivariant
closed-inclusion transport of semigroup subgroups and the identity between
the positive cyclic semigroup functor and the root functor. Each also maps
into the `B` subgroup because it factors through `U`. Lifting the supplied
point to `U`, applying the inverse ordered-product isomorphism, and using
its product compatibility gives the required tuple and product equation.

For coordinatewise detection, this tuple is compared with the supplied
one using uniqueness of ordinary `A` coordinates from
`RootSubgroupTorusProduct`. The reverse implication is closure of the `B`
subgroup under finite products. For the final theorem, existence packages
the constructed coordinates in intersection subtypes; uniqueness follows
from the same ordinary `A` coordinate uniqueness and subtype extensionality.

The provenance is internal: this is a deduction from the existing actual
semigroup realizations, unipotent ordered products and selected-root
factorizations. It introduces no new assertion from literature. The upper
opposite-factor-pair assumption remains explicit. The unit does not assert
the lower doubled-root valuation axiom, a full lower valuation, or
`BuildingComparisonStatement`.
