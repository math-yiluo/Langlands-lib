# Multiplicative-type Weyl quotients from centralizer quotients

This internal adapter works over an arbitrary scheme, with a smooth relatively
affine ambient group and a closed multiplicative-type subgroup. It constructs
the Weyl group quotient once the relevant homogeneous centralizer quotient
is supplied. The existence input remains explicit.

Every supplied normalizer representative is closed, by comparison with the
published chosen closed normalizer. The original multiplicative-type subgroup
factors as a closed subgroup of that representative, and the centralizer of
this internal subgroup is exactly the preimage of the original centralizer.
Monomorphisms reflect the all-test commutation relation.

For any representative of this centralizer preimage and any supplied actual
homogeneous quotient by it, the centralizer is normal in the normalizer on
every test scheme. The published homogeneous quotient group construction
therefore descends a group structure and a group projection with the exact
prescribed fppf kernel. The normalizer is smooth by the multiplicative-type
normalizer theorem, and its centralizer inclusion is open. The published
open-subgroup quotient theorem gives an etale structure map for the descended
group. Separatedness and quasi-compactness come directly from the supplied
homogeneous quotient.

The final adapter takes centralizer-quotient existence inside the actual
normalizer as an explicit argument. Applying it to the factored subgroup
gives the required homogeneous quotient, and the preceding construction
gives the separated quasi-compact etale group quotient. This reduces that
part of the host target to centralizer-quotient existence; it does not assert
unconditional existence of either the ambient centralizer or normalizer
homogeneous quotient.
