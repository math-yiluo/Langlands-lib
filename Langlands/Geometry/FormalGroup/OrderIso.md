# Actual formal isomorphisms commuting with an acting order

This internal module upgrades an actual formal `O`-module
isomorphism to an actual full-order isomorphism when its forward
formal map commutes with the given order actions. The scalar ring
and coefficient ring are arbitrary commutative rings with the given
algebra structure. The acting order is any algebra ring, and the
finite source and target coordinate types may differ.

`Iso.inverse_commutes` proves order commutation of the actual inverse
by inserting the forward/inverse pair, applying the supplied
forward commutation equation, and cancelling the inverse pair.
`Iso.ofModuleIso` retains those same two formal maps and their
two-sided inverse equations. It does not choose a new inverse or
assume inverse commutation.

The supporting full-order Hom identity and associativity laws follow
from the underlying actual formal Hom laws. `Iso.refl`, `Iso.symm`
and `Iso.trans` construct actual identity, inverse and composite
full-order isomorphisms, and their underlying formal-module
isomorphisms are precisely the corresponding existing constructions.
Inverse uniqueness and forward-map extensionality also follow from
the actual formal inverse equations.

The provenance is internal from `OrderAction` and the actual
formal-module map and isomorphism definitions. No rationalization,
height, nilpotence, representability or coefficient-descent
hypothesis is required.
