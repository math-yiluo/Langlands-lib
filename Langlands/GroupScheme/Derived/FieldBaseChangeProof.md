# Field base change for the scheme-theoretic derived subgroup

Author: Worker 1449.

This module supplies the restriction-core construction used in the proof of
`DerivedSubgroupFieldBaseChangeStatement`. The construction and its proofs are
internal consequences of the published subgroup-functor definitions, the
pullback adjunction on points, and the universal closed-factorization locus.
The exact field-base-change theorem is assembled in `FieldBaseChangeAssembly`.
Its source assertion is Milne, *Algebraic Groups* (2017), Corollary 6.19(a),
printed p.129 / PDF p.145, registered source
`milne-2017-algebraic-groups`. The argument here uses closed factorization
rather than the book's generated-subgroup proof.

For a map of base schemes `b : S' → S` and a subgroup functor `F` of `G` after
base change, `SubgroupFunctor.restrictionCore b F` consists of those
`g : T → G` such that for every `S'`-scheme `T'` and every map from its
underlying `S`-scheme to `T`, the corresponding point of the pullback of `G`
belongs to `F(T')`. Stability under restriction follows by composition.
The multiplicative pullback point equivalence carries products, inverses and
identity points to their counterparts, proving that these sets form a
subgroup functor. The same compatibility proves
`ContainsCommutators.restrictionCore`: if `F` contains all commutators, so
does its core. Applying core membership to the identity refinement proves
`restrictionCore_baseChange_le`.

For an inclusion `i : H → G` over `S'` after base change, the auxiliary maps
`restrictionCoreLeft` and `restrictionCoreMap` regard its underlying map as
a morphism into `S' ×_S G`, using the symmetry of the chosen pullback.
`restrictionCoreMap_isClosedImmersion` proves this map is closed when `i`
is closed, by composing with that symmetry isomorphism.

`mem_restrictionCore_range_iff` identifies the all-refinement core condition
with the factorization of the entire product map
`S' ×_S T → S' ×_S G` through `H`. In the forward direction it tests core
membership on `S' ×_S T`, regarded over `S'`, with the projection to `T`.
In the reverse direction an arbitrary refinement maps to that product by
its structural map and its given map to `T`. Composing with the
factorization gives a point of `H`; the two pullback projection equations
establish both its structural compatibility and its image under `i`.

Finally, `restrictionCore_isClosedRepresentable` assumes `S = Spec k` for
an arbitrary field `k`, an affine map `b`, an affine structural map for `G`,
and a closed representative for `F`. It applies
`ClosedFactorizationLocusProof.affine` with parameter scheme `S'` and
target `G`. The parameter's coordinate module satisfies
`HasFpqcProjectiveCoordinateModule` by taking the faithfully flat extension
`k/k`: every module over the field `k` is projective. The factorization
equivalence identifies the resulting closed locus with the core on every
test scheme. `isClosedRepresentable_of_scheme` then transfers the subgroup
law to that representing scheme and constructs the closed group-scheme
inclusion.

The closed-representability helper requires no flatness or finiteness
hypothesis on `b`, and no finite type hypothesis on `G`. The definitions
and factorization equivalence quantify over all test schemes of the given
universe, including nonaffine and nonreduced schemes.
