# Sheaf transport through homeomorphisms across universes

This module is an internal categorical construction from Mathlib's open-set
order isomorphism of a homeomorphism and actual ordinary sheaf topologies.
Space and coefficient universes remain independent.

The open-set equivalence preserves covering sieves: a member covering the
inverse image of a point gives a member covering that point. Both directions
are therefore continuous. Precomposition gives an equivalence of the actual
sheaf categories, with the unit and counit obtained by whiskering those of the
open-set equivalence.

`uliftEquivalence` specializes this construction to the canonical homeomorphism
between a space and its universe lift. The section formula is literal evaluation
on the inverse-image open. No cohomological comparison is assumed.
