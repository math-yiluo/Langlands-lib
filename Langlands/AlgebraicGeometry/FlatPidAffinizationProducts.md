# Products of canonical affinizations over a PID

This internal construction identifies the actual product comparison of the
functor `algΓ R ⋙ algSpec R`. Its value on a scheme over `Spec R` has precisely
the prescribed structural map from the spectrum of global functions; on a
morphism it is the spectrum of the induced global-section map.

The terminal comparison is an isomorphism for every commutative base ring.
For flat quasi-compact separated schemes over a principal ideal domain, the
canonical binary product comparison is an isomorphism as well.
`affinizationProductIso` supplies that actual over-base isomorphism.

The proof uses `FlatGlobalSectionsProduct.isPushout_appTop_pid`, applies the
spectrum functor to obtain a pullback, and changes the affine base using the
spectrum/global-sections isomorphism of `Spec R`. The resulting comparison is
the canonical map into the pullback, so its underlying map is an isomorphism;
the forgetful functor from schemes over the base reflects isomorphisms.
Neither factor is assumed affine, and no finite generation is required.

The application is the natural group structure on `Spec Γ(G, O_G)` used in
Prasad–Yu, *On quasi-reductive group schemes*, author preprint p.5,
Proposition 3.1. This module's PID generality and categorical comparison are
internal auxiliary results, rather than assertions that the source states them
in this form.
