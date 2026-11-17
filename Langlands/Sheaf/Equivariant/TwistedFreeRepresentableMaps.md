# Natural maps between free globally lifted representables

This internal construction starts with two supplied whole-group lifts and an
ordinary arrow between their represented objects. `IsEquivariant` is the
explicit intertwining equation for those lifts. It is preserved by identities
and composition.

`precomp_postcomp` proves that normalization of a twisted restriction commutes
with postcomposition by this arrow, using its intertwining equation.
`presheafMap` therefore defines a natural transformation between the actual
normalized ordinary-Hom-valued presheaves. Identities and compositions are
preserved. `presheafMap_restriction` identifies ordinary restriction with the
given ordinary Yoneda map.

Applying the free module sheaf functor gives `freeSheafMap`, again preserving
identities and compositions. Naturality of the free-sheaf adjunction and of the
fixed-section equivalence shows that precomposition by this map restricts the
represented section along the original ordinary arrow.

For a local action system consisting of lifts, assume finite equivariant
refinements and eventual equivariance of the two represented objects.
`discreteFreeSheafMap` packages the same free sheaf map in the actual discrete
sheaf category. Its identity, composition and fixed-section naturality laws
follow by forgetting to the full subcategory's underlying sheaf maps. Each
eventual-equivariance proof remains an explicit input.

With ordinary and twisted module sheafification and the pointwise right Kan
extensions required for the existing restriction comparison, the theorem
`freeSheafMap_restriction` proves that the induced map restricts to the actual
ordinary free representable map through those specified comparison
isomorphisms. The proof compares represented sections using the injective
ordinary free-representable equivalence and its restriction identity.

All geometric actions and their intertwining equation are supplied. No
analytic existence or compatibility result, exact Čech model, or global
cohomology comparison is asserted.
