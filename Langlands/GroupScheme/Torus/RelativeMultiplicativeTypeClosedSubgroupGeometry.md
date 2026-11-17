# Geometry of closed subgroups of relative groups of multiplicative type

This internal supporting unit supplies affineness and commutativity for a given closed subgroup of a group satisfying the published arbitrary-base predicate `RelativeMultiplicativeType.IsMultiplicativeType`.

For every scheme `S` in the arbitrary universe `u`, groups `H K : GroupScheme S`, proof `hH : IsMultiplicativeType H`, and homomorphism `k : K ⟶ H` whose underlying scheme morphism is a closed immersion:

- `IsMultiplicativeType.closedSubgroup_isAffineHom hH k hk` proves that the structure morphism of `K` is affine.
- `IsMultiplicativeType.closedSubgroup_isCommMonObj hH k hk` proves that the actual group object `K.X` is commutative.
- `IsMultiplicativeType.closedSubgroupCommGroupScheme hH k hk` packages the same `K` as a `CommGroupScheme S`. Its underlying group scheme is definitionally `K`.

The proof uses only published predicate and descent modules. Private helpers derive the ambient geometry from the actual fppf diagonalizing cover in the relative multiplicative-type predicate. The split model is affine because it is the base change of the spectrum of the group algebra over the integers; it is commutative because the original diagonalizable model is a commutative group object and base change preserves this property. Isomorphisms transport these facts to diagonalizable groups. Published fppf locality of affine morphisms and `isCommMonObj_of_fppfCover` then descend them to `H`.

The structure morphism of `K` is the composite of its closed immersion into `H` and the affine structure morphism of `H`, hence is affine. For commutativity, closed immersions are monomorphisms: for every test scheme, the two products in `K` become equal in the commutative group of `H`-valued points and therefore are equal in `K`. The constructor adds this proved commutativity to the original group scheme.

No flatness or finite-presentation hypothesis is imposed on `K`. The unit does not assert that an arbitrary closed subgroup itself satisfies the relative multiplicative-type predicate.

Provenance: these are derived adapters from the published relative diagonalizable and multiplicative-type definitions, the published fppf descent results, and Mathlib's base-change and monomorphism properties. The ambient geometry helpers are private so that this unit can coexist with a separate general relative multiplicative-type geometry module; it exports only the closed-subgroup API above.
