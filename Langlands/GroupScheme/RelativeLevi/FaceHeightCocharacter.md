# Coordinate cocharacters realizing multiples of face heights

This derived helper extends an integral linear form on the integral root span
of a coordinate root datum to the full coordinate character lattice after
multiplication by a positive integer. No spanning or semisimplicity assumption
on the root system in the full lattice is imposed. A base of the root datum
is supplied.

`exists_coPairing_eq_rootSpanLinear` first assigns the required values to the
linearly independent simple roots over the rationals. The resulting functional
on their rational span extends to the full rational coordinate space using
`Subspace.dualLift`. Clearing the finitely many coordinate denominators and
multiplying again by the same nonzero denominator gives an integral coordinate
cocharacter with positive multiplier equal to the square of that denominator.
The equality holds on every element of the integral root span, by the integral
simple-root basis.

`RootSpanCocharacterRealization` records an actual coordinate cocharacter,
a positive integral multiplier, and the exact pairing equation on the whole
root span. `rootSpanCocharacterRealization` chooses such data from the proved
existence theorem. `faceHeightCocharacterRealization` chooses the specialization
to the published integral face height. These constructions let later consumers
use one fixed multiplier and cocharacter together with their equality witness.

`exists_coPairing_eq_faceHeight` applies this construction to the published
`RootDatumFaceHeight.faceHeight`. In particular, the values on all roots equal
one fixed positive multiple of the canonical integral face height. The theorem
does not claim that this multiplier or the extending cocharacter is canonical.
It needs no dominance hypothesis because it asserts realization only.

Provenance is the rational-extension and denominator-clearing method of the
existing `LocalSplitCell.exists_coPairing_eq_height`, generalized from the
constant simple-root value one to an arbitrary integral linear form, together
with the existing integral simple-root basis and face-height definition. The
intended use is to cancel the positive multiplier in root commutator weight
bounds, leaving unscaled canonical integral face weights.
