# Actual central products from a derived-torus complement

This internal construction forms the genuine group homomorphism multiplying
the central complement of a compatible derived-torus map with the supplied
subgroup. If the prescribed subgroup and ambient torus have surjective
multiplication, the new central product is surjective as a scheme morphism.

The proof pulls back the complement's surjective product along the subgroup,
then factors the resulting multiplication through the central product. The
factor sends `(d,t,z)` to `(z,d j(t))`; compatibility and all-test centrality
identify the two maps. Surjectivity of the composite implies surjectivity of
the central product. For connected reductive source subgroup and ambient
group, the published flatness theorem for a surjective group homomorphism
also gives flatness.

All complement data, compatibility, and product surjectivity are supplied
explicitly. This construction does not prove their unconditional existence or the host
root-model proposition. In particular it does not yet derive semisimplicity
from the central product.

`DerivedTorusCentralComplement.centralProduct` is the actual homomorphism.
`centralProduct_hom` identifies its underlying map with `subgroupProductMap`.
`surjective_centralProduct` takes the compatible map `j`, its exact square,
and surjectivity of the supplied subgroup and torus multiplication.
`flat_centralProduct` additionally takes connected reductivity of both
the ambient group and the supplied subgroup. All statements preserve the
arbitrary field and universe. The complement is fixed throughout.
