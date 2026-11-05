# Full pullbacks identified by a self-centralizing subgroup

Author: Worker 1669. The composite-map interface was developed in
coordination with Worker 1614.

This is an internal comparison construction for the full maximal-torus
preimage problem. Its provenance is the universal property of the actual
categorical pullback and the published all-test subgroup-functor and torus
centralizer definitions. It asserts no new structural theorem about maximal
tori of reductive groups.

Over any base scheme, suppose `p : C → H`, `i : T → H`,
`j : A → C` and `f : A → T` are homomorphisms, where `A` and `T` are
commutative group schemes, and `j ≫ p = f ≫ i`. Assume that the full
centralizer of `j` in `C` is its range, and that the first projection of
`C ×_H T` has range contained in that centralizer.

`range_subgroupIntersectionFst_eq_of_selfCentralizing` identifies the range
of this projection with the range of `j`. One inclusion uses the supplied
centralizer containment and equality; the other uses the pullback lift
of `j` and `f`. When `i` and `j` are closed subgroup inclusions,
`selfCentralizingSubgroupIntersectionIso` constructs an isomorphism from
the actual pullback to `A`. The two following lemmas say that the forward
and inverse maps preserve the inclusions into `C`.

The centralizer-containment hypothesis can be discharged in a composite
setting. Let `π : C → D` and `d : D → H`, with the underlying map of
`d` monomorphic, and suppose `j ≫ π ≫ d = f ≫ i`. Retain the explicit
centralizer-reflection premise

```lean
(torusCentralizer (j ≫ π)).comap π = torusCentralizer j
```

Then `range_subgroupIntersectionFst_le_torusCentralizer_of_reflection`
shows that the first projection of `C ×_H T` centralizes `j`. On every
test scheme and every refinement, both images in `H` come from `T` and
commute. Monicity of `d` reflects their commutation to `D`; the displayed
premise reflects membership in the whole torus centralizer back to `C`.

Over an arbitrary field, the final theorem
`isTorus_subgroupIntersection_of_selfCentralizing_of_reflection` applies
this construction when `A` is a torus, `i` and `j` are closed inclusions,
and the self-centralizer and reflection equalities are supplied. It
transports `IsTorus` through the constructed group-scheme isomorphism.
The target `T` need only be commutative in this comparison.

All functor equalities are tested on every scheme over the base, including
nonreduced schemes. The pullback is the full scheme-theoretic pullback.
There is no passage to a reduced subscheme, an identity component, or
geometric points. This conditional construction does not prove
`DerivedCoverMaximalTorusPreimageStatement`: applying it still requires
construction of a suitable source torus and proof of its
self-centralizer and centralizer-reflection properties.
