# Multiplication of commuting subgroup schemes

Worker 1466.

This is an internal adapter for the published `subgroupMultiplication` scheme
morphism. For arbitrary group maps `j : H ⟶ G` and `i : K ⟶ G` over any base,
assume their images commute on every test scheme. The theorem
`subgroupMultiplication_mul` proves multiplicativity by expanding the two
coordinates and interchanging the middle commuting factors.
`commutingSubgroupMultiplicationHom` packages the same underlying morphism as
an actual homomorphism from the direct product group scheme `H ⊗ K`.
Its underlying relative scheme map is definitionally `subgroupMultiplication j i`.
The two range-containment lemmas lift a factor point to the product by
putting the identity in the other coordinate, and thus prove that its image
contains both factor images on every test scheme.

Over an arbitrary field in universe `u`,
`subgroupMultiplication_flat_of_surjective` assumes that both factors are
quasi-compact and locally of finite type, the target is smooth, and this
multiplication is surjective as a scheme morphism. The product inherits the
source finiteness properties from the pullback presentation. The published
`flat_of_surjective` theorem then proves flatness of the same multiplication
map. The factors need not be smooth. This file does not prove surjectivity.

The specialization `subgroupMultiplication_flat_of_closedSubgroups` assumes
that the target is smooth and affine and both maps are closed subgroup
inclusions. The composites with the target structure morphism make both
sources quasi-compact and locally of finite type. It applies the preceding
adapter, so the complement's smoothness is still unnecessary.
