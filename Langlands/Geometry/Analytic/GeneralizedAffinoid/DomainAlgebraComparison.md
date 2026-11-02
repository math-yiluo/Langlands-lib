# The actual stored algebra maps to finite rational descent

Author: Worker 36.

This construction gives the canonical comparison from the stored algebra of a
full represented affinoid domain to the section algebra of the
finite-rational-descent extension.

`algebraToExtension K A U` is the map to the explicit finite
multiequalizer induced by the actual bounded restrictions from `U.algebra`
to the chosen ambient rational cover. The actual pairwise intersection
arrows commute over the full domain, so these restrictions satisfy the
multiequalizer equations. `algebraToExtension_projection` identifies every
projection with the original stored bounded restriction.

`algebraToExtension_restriction` extends that equality to every actual
arrow from a rational domain. The proof checks equality on a covering
sieve of rational arrows factoring through the chosen cover. Full
faithfulness turns Mathlib's locally constructed rational restriction
into the actual stored bounded map; the original rational algebra sheaf
then gives uniqueness.

`algebraToExtension_naturality` proves commutation with every full-domain
restriction. It tests the equality after the finite rational projections,
uses the extension's restriction formula, and applies the preceding
arbitrary rational restriction identity. `algebraToExtensionNat` packages
these maps as an actual natural transformation from the retained
algebra presheaf to the underlying presheaf of the extension.

`algebraToExtension_rational` identifies the comparison on every rational
image domain with the inverse of `rationalSectionIso`. The proof compares
the finite projections of the two algebra maps. Mathlib's explicit formula
for the inverse gives its locally constructed rational restriction, which
full faithfulness identifies with the original actual bounded restriction.
The instance `algebraToExtension_rational_isIso` records the resulting
isomorphism on each rational image.

This construction is an internal derivation using the actual domain
category, rational algebra sheaf and explicit dense-subsite extension.
No new literature assertion or private peer draft is reused. It does not
yet assert that the comparison is an isomorphism for every full domain.
