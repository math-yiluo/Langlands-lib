# Ordered actual root products for selected character semigroups

This is an internal construction from existing Library results. All fields and
schemes have an arbitrary universe parameter `u`. Let `G` be a smooth affine
group scheme over a field `k`, let `T` be a split torus, and let `i : T → G` be
a homomorphism. For the ray and product theorems, the underlying scheme map of
`i` is monomorphic and `HasOppositeFactorPairs i` is supplied. The latter is the
existing existence condition for opposite factors at every nonidentity
rational root point. Its existence is not proved here. Ambient reductivity,
ambient connectedness and maximality of `T` are not hypotheses.

Let `A` be an additive subsemigroup of the character lattice of `T`.
`semigroupIndivisibleRoots i A` consists of actual roots `a` in `A` such that
no actual root `b` in `A` satisfies `m • b = a` for an integer `m > 1`.
Indivisibility is taken within the selected roots. This permits a root `2b`
to index a selected ray when `b` itself is excluded from `A`.

The supporting declarations have the following meanings.

- `cyclicTail_one_le_of_mem` says that `a ∈ A` puts every positive integral
  multiple of `a` in `A`. This uses only additive semigroup closure.
- `exists_semigroupIndivisibleRoot_ray` puts each actual root in `A` on the
  positive integral ray of a selected indivisible root.
- `disjoint_cyclicTail_semigroupIndivisibleRoots` says that distinct selected
  indivisible roots have disjoint positive integral rays.
- `iUnion_rootRayBlock_semigroup` identifies the union of the actual root
  blocks of an exact finite enumeration of those roots with
  `relativeRoots i ∩ A`. `rootRayBlock_semigroup_pairwise` supplies both
  disjointness and the cross-exclusion against the additive closure of every
  other block.
- `actionWeightSupport_semigroupSubgroup_eq_roots_inter` identifies the full
  action support of the existing semigroup subgroup with that same intersection
  when `0 ∉ A`. This support equality does not require monomorphy or opposite
  factor pairs.
- `exists_semigroupIndivisibleRoots_enumeration` supplies an injective finite
  enumeration, using the proved finiteness of actual roots for a split torus
  acting on a smooth affine group. It also does not require opposite pairs.

For any such enumeration `a : Fin n → characterLattice T`,
`semigroup_orderedRootProduct` constructs actual group schemes `U`, `H r`,
homomorphisms `jU : U → G`, `j r : H r → G`, and an isomorphism of schemes
over `k`

`e : (∏ᶜ H).X ≅ U.X`.

Here `jU` represents the existing subgroup functor
`semigroupSubgroup (conjugation i) A`, each `j r` represents the existing
intrinsic root functor `subgroup i (a r)`, and

`e.hom ≫ jU.hom.hom = orderedMultiplication j`.

The representatives and maps are actual schemes and homomorphisms. All the
inclusions are closed, and `U` and every `H r` are smooth, connected, unipotent
and split unipotent. The isomorphism is asserted for the underlying schemes:
ordered multiplication need not be a group homomorphism. Representation is
equality of subgroup functors on every scheme over `k`, including nonreduced
tests. The case of an empty selected root set is included.

The implemented proof first uses
`HasOppositeFactorPairs.eq_one_or_two_of_nsmul_mem` to bound division of an
actual root. A nonminimal selected root must be twice another selected root;
a second division would give a root multiple greater than two. Thus the
selected rays cover. The common-positive-multiple theorem in
`RootRayFromFactorPairs` forces two roots on intersecting rays to be equal or
one to be twice the other. Selected indivisibility excludes the latter two
possibilities and proves disjointness.

For the product, `semigroupRealization` gives a smooth connected closed
representative `U` of the existing semigroup subgroup. Exclusion of zero makes
`U` split unipotent. Its induced `T` action has exactly the selected root
support, by equivariance of the inclusion and the support equality above.
`hasOrderedSemigroupProducts_of_unipotent` applied to the selected ray blocks
therefore gives an ordered product inside `U`. Equivariant closed-inclusion
transport identifies the ambient image of each factor with the cyclic
semigroup subgroup. The published
`weightFiltration_one_eq_subgroup` identifies that subgroup with the actual
root functor. Composing the factor inclusions with `jU` and using
`orderedMultiplication_comp` gives the displayed equation. The cyclic
realization theorem also supplies unipotence and splitness of each factor.

This unit constructs a selected-root product, not the final
`BuildingComparisonStatement`. It supplies neither initial opposite pairs
nor compatible valuation data, a building metric, a special point for the
supplied integral model, or unique fixation.
