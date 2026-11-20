# Changing the original affine base of a projector homomorphism

Successive pullback of the diagonalizable and general linear groups is identified with direct pullback through `affineModelComparison`, using a supplied isomorphism on the intermediate affine base. The pullback adjunctions preserve the projection of a point to the original group. The comparison of the underlying test schemes is the identity, so it preserves the global character values and matrix entries.

For a projector family on the final affine base, the two homomorphisms have the same weighted matrix on every test scheme. This proves `subgroupHom_affineModelComparison` for arbitrary weights. When the weights generate the character group, `isClosedSubgroup_subgroupHom_spec` shows that these homomorphisms are closed immersions. The comparison is used to pass from the affine ring of an étale splitting chart back to the original base of the moduli.
