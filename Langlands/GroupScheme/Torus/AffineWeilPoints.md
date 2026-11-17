# Weil points over an affine base with actual global-section scalar maps

This internal derived module identifies the points of the actual Weil group
over an affine scheme with tensor units using the structure map's direct action
on global sections. It removes the intervening spectrum/global-section algebra
identification from the coefficient formulas.

`sections` uses the actual structure morphism's global-section ring map.
`sectionsEquiv` identifies it with the usual spectrum-based algebra by the
identity on the underlying ring, using the affine unit-counit identity.
`sectionsMap` is the actual global-section restriction map.

`group` is the pullback of the Weil group from the spectrum of the affine base's
global-section ring. `pointsEquiv` combines the pullback point equivalence,
Weil point model and scalar-compatible identity of section algebras.
`tensorSectionsEquiv_naturality` and `pointsEquiv_naturality` prove naturality
on every relative test morphism by pure-tensor calculations.

The coefficient algebra is finite projective over the affine base's global
sections. The universe is arbitrary and no nonzero-ring assumption is made.
This module does not supply a permutation-atlas group comparison.
