# Affine restriction of actual identity-jet quotients and layers

This auxiliary module identifies restrictions of the actual identity-jet sheaf
with restrictions of actual augmentation residue classes. Let `G` be an affine
group scheme over an arbitrary scheme `S`. No smoothness or constant-rank
hypothesis is used.

For an inclusion `V ≤ U` of affine base opens, `IdentityJet.restriction G n h`
is semilinear along the actual structure-sheaf restriction
`Γ(S,U) → Γ(S,V)`. It is obtained by transporting the actual jet-module
restriction through `IdentityJet.sectionsEquiv`. The theorem
`sectionsEquiv_restrict` states this comparison square.

The theorem `restriction_mk` computes this map intrinsically: the class of an
actual function on `G` above `U` goes to the class of its restriction above
`V`. Its proof uses naturality of the actual quotient-map morphism of module
sheaves and the existing computation of `sectionsEquiv` on that morphism.
Surjectivity of the ring quotient then proves `restriction_truncate`, the
commutative square for successive actual augmentation quotients.

Applying the order-zero restriction to a vanishing residue class proves
`augmentation_functionRestriction_eq_zero`: restriction preserves functions
vanishing at the actual identity. The map `layerRestriction` is consequently
the induced semilinear map on the actual kernels of successive truncations.
Its value is the restriction of the ambient residue class.
`layerRestriction_homogeneousToLayer_val` applies the residue-class formula
to homogeneous coordinate evaluation; it asserts this value formula and does
not assert that a coordinate family remains a basis after restriction.

The provenance is internal: all maps and computations follow from the actual
identity-jet sheaf, its quotient map and the algebraic augmentation filtration
already defined in the imported modules. This module supplies restriction
compatibility for later determinant comparisons; it proves no determinant-line
isomorphism or ampleness statement.
