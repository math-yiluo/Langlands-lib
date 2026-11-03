# Represented fppf-local subgroup products

This module defines ordered product membership and a predicate for its
representation by an actual closed subgroup scheme. It works over every
`S : Scheme.{u}`, for arbitrary universe `u`, using the Library's
`GroupScheme S` and `SubgroupFunctor`. It constructs no representing scheme.

## Source and provenance

The algebraic-group application is the subgroup product in
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
Definition 2.2.1 and Example 2.2.2, printed p.62 (PDF p.88). The registered
source is `conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
There the product combines the dynamic parabolic with the ground-field
unipotent radical.

The single-cover membership formula and the generic predicate names are an
internal sheaf-theoretic formulation of that subgroup product, rather than a
verbatim definition in CGP. For represented factors, multiplication defines a
map from their scheme product to the ambient group. A point is in its fppf
sheaf image when its pullback admits a lift locally for the fppf topology.
The formula below expresses that local lifting condition directly, including
the factorization equation. A family of fppf covering maps can be combined into
its disjoint-union map, giving one flat surjective locally finitely presented
cover; no quasi-compactness or affineness condition is added. This explains the
single-cover formulation on all tests.

For arbitrary subgroup functors, the formula itself is the definition; the
module does not prove that it is a subgroup or an fppf sheaf. Instead,
`IsFppfProduct` asks for a closed subgroup whose image has exactly that
membership formula. In particular, it does not assert that every pair of
subgroup functors has such a representative. The application to pseudo-parabolic
subgroups retains the radical's normality in its separate radical predicate.

## Definitions

For subgroup functors `F,N` of `G` and an actual point `x : T ⟶ G.X`,
`FppfLocallyInProduct F N x` means there are:

- a relative scheme `V : Over S` and a morphism `v : V ⟶ T`;
- proofs that `v.left` is flat, surjective, and locally of finite presentation;
- actual points `p,n : V ⟶ G.X`, with `p ∈ F.carrier V` and
  `n ∈ N.carrier V`;
- the equation `v ≫ x = p * n` in the group of `V`-valued points.

`V` and `T` range over all relative schemes, including nonaffine and nonreduced
ones. The factors need only exist after the cover. Neither pointwise product
membership on the original test nor a pointwise subgroup join is substituted
for this condition.

`IsFppfProduct F N (i : P ⟶ G)` is a proposition with two fields:

- `isClosedSubgroup : IsClosedSubgroup i`, so the underlying scheme map is a
  closed immersion;
- `mem_range_iff`, identifying membership in the existing
  `SubgroupFunctor.range i` with `FppfLocallyInProduct F N x`, for every `T`
  and every `x : T ⟶ G.X`.

Thus a point of `G(T)` factors through the closed inclusion precisely when it
can be written as an ordered product after some such cover. A lift to `P`
over the original test does not come with a factorization there. The predicate
specifies represented fppf-image membership; representability and any comparison
with another construction of a scheme image are separate mathematical issues.

## Proved elementary consequences

The following consequences are proved, rather than additional definitional
fields:

- `FppfLocallyInProduct.of_mul` uses the identity map of `T` as the cover for
  a product already defined over `T`. Identity morphisms have the three required
  properties.
- `FppfLocallyInProduct.of_left` and `.of_right` take the other factor to be
  the identity point.
- `FppfLocallyInProduct.mono` retains the same cover, points and equation
  when either subgroup functor is enlarged.
- `IsFppfProduct.left_le` and `.right_le` apply `mem_range_iff` to the preceding
  identity-factor constructions and give all-test image inclusions.
- `IsFppfProduct.range_eq` compares the two membership equivalences pointwise
  and applies subgroup-functor extensionality.

These proofs need no product-existence theorem, no quotient construction,
and no surjectivity of a multiplication map on the point group of an original
test scheme.
