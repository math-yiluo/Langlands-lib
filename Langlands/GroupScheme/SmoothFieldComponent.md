# Finite-type identity components of smooth field groups

This internal derived construction supplies the actual identity component of a
smooth group scheme over an arbitrary field, without assuming affineness or
quasi-compactness of the ambient group. It uses the published raw component
restriction and product-covering theorem in `RelativeIdentityComponent`.

`quasiCompact_of_smooth_connected` proves that a smooth connected group scheme
over a field is quasi-compact. Choose an affine open neighbourhood of the unit
and take the actual multiplication map on the product of two copies of this
open. `identitySet_subset_range_fieldOpenProduct` says that its image contains
the identity component. Connectedness of the ambient group makes that component
the whole group. The product has compact underlying space, so its surjective
continuous image is compact, yielding quasi-compactness of the structure map.

`SmoothFieldComponent.group H` puts the restricted group law on the raw open
component `fieldIdentityOver H`. Its `inclusion` is an actual group-scheme
homomorphism, both an open and a closed immersion, with topological range
exactly the connected component of the unit. The closedness follows from the
closedness of a topological connected component and the existing open immersion.
Multiplication and inversion factor through that inclusion by connectedness;
the group-object descent construction verifies the group axioms through the
monomorphism.

The constructed group is smooth, connected, geometrically connected,
geometrically integral and quasi-compact, hence of finite type over the field.
Its quasi-compactness follows from the new smooth connected consequence, and
its geometric integrality from published smooth geometric integrality.
`factor H f` factors every actual homomorphism from a connected group scheme
through the inclusion, with `factor_inclusion` giving the equality over `H`.
No smoothness or finiteness hypothesis is imposed on this connected source.

These are derived consequences and constructions using published
`RelativeIdentityComponent.FieldGeometry`, `FieldProductCover`, the
`IdentityComponent` open-immersion factorization, and group-object descent.
They supply geometry for the smooth radical extension task; this file does not
assert that extension target.
