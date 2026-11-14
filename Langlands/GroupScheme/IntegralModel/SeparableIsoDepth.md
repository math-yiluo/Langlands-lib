# Transported separable additive depth models

This derived construction transports `separableDepthVector` through an actual
isomorphism from a generic group `U` to the polynomial vector group of a finite
separable extension `E/K`. The base has a surjective integer-valued
multiplicative valuation and a Henselian valuation ring. The extension may have
an independent universe and may be ramified.

`separableIsoDepthModel` retains the integral polynomial vector group and
composes its generic identification with the inverse supplied isomorphism.
Its integral-point image is exactly the actual normalized valuation-depth
lattice, with the field element obtained by applying the supplied isomorphism
and reading its coordinates in the fixed basis of `E/K`. The membership proof
cancels the generic isomorphism in the retargeted point image and uses the
previously proved exact depth-lattice membership criterion.

The models are smooth and have geometrically connected fibres.
`separableIsoDepthTransition` retains the actual integral matrix of the deeper
lattice's inclusion into the shallower lattice. Its generic compatibility
follows by composing the original matrix equation with the inverse
isomorphism. Generic rigidity identifies every other extension of the identity
with this explicit map. Thus `separableIsoDepthModel_kernel_properties` reduces
its actual scheme-theoretic special-fibre kernel to the established
`separableDepthVector_kernel_properties`.

The provenance is transport of the additive models underlying Kaletha–Prasad,
*Bruhat–Tits theory: a new approach* (2023), Appendix C.2 and the additive case
of Appendix C.5. This module assumes no root-filtration comparison and makes
no assertion about an independently supplied apartment or integral model.
