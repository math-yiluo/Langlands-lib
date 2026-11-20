# Equality of group homomorphisms on an open neighbourhood of the unit

Worker 606.

Let `G` be a smooth group scheme over an arbitrary base with connected
residue fibres and let `P` be an open containing the whole unit section.
`unitOpenMultiplicationCover` is the one-member smooth cover of `G` given
by the multiplication map from the fibre product of `P` with itself
over the base.

The relative identity set contains every point of `G` by connectedness of
the residue fibres. The existing product-image theorem therefore makes
the multiplication of two copies of the open surjective. The product
inclusion is an open immersion and multiplication on `G` is smooth, so
restricted multiplication is smooth.

The theorem `hom_ext_of_comp_unitOpen_eq` uses this cover to show that two
homomorphisms from `G` to any group scheme over the same base agree if
their restrictions to `P` agree. The cover map is an epimorphism over
the base by flatness and surjectivity. The homomorphisms agree after
precomposition with it because both preserve multiplication.

This is an internal consequence of `underlyingSet_subset_range_product`
and `smooth_multiplication`. In a jet centralizer argument it applies after
equality of conjugation and the identity has been established on a unit
neighbourhood.
