# Split-torus cocycles over fields

`Cocycle.isTrivial_of_isSplitTorus_overField` says that a cocycle of a split torus over the spectrum of any field, on any affine flat surjective cover, is a coboundary on that same cover. The group and cover are the actual supplied objects; no separability or finite-type condition is imposed on the cover. The identity holds after every test scheme, with the convention `ξ(a,b) = f(a) f(b)⁻¹` of `Cocycle.IsTrivial`.

This is an internal specialization of the published `Cocycle.nonempty_localTrivialization_of_isSplitTorus` from `Torus.OpenSections`. Choose the unique point of the field spectrum. The helper `Cocycle.opens_eq_top_of_field` proves that any open containing that point is the whole base, using the subsingleton property of the field spectrum. Hence the inverse image of the local trivialization's open is the whole cover. Its inclusion is an isomorphism of schemes and therefore an isomorphism in the over category. Composing the local cochain with its inverse gives the required cochain on the original cover, and the local all-test coboundary equation becomes the desired equation by cancellation of that isomorphism.

`Cocycle.fieldTrivializingCochain` chooses a cochain from this existence theorem. `Cocycle.fieldTrivializingCochain_spec` records its all-test coboundary identity, so downstream constructions can use one fixed choice.

This unit supplies cocycle trivialization only. The transporter and normalizer descent needed by the reductive-group application is a separate step.
