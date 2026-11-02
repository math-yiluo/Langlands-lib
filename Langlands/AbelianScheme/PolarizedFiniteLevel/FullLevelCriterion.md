# Full level as an actual torsion-enumeration isomorphism

This internal converse to `FullLevelTrivialization` concerns an already
supplied ordered tuple of actual global torsion sections. It uses the
existing `IsFull` definition unchanged.

If its actual enumeration map `torsionCoproductMap` is an isomorphism,
then restriction of the sections gives a bijection between coefficient
tuples and actual kernel points over every field-valued base point.
Injectivity follows from the isomorphism and the disjointness of scheme
coproduct components. For surjectivity, compose a field-valued kernel
point with the inverse enumeration map. The spectrum of a field has one
point, so this map lands in one coproduct component. That component is
open, hence the map lifts to it. Its structure equation over the base
identifies the lift with the given base point.

The generic kernel universal-property comparison identifies this
bijection with the residue-linear combination map of the restricted
tuple. A bijective linear map gives a linear equivalence, and its inverse
coordinates give the required basis with the prescribed entries.
`fullLevelOfTorsionCoproductIsIso` packages the resulting `FullLevel`
without changing the tuple. The converse construction needs neither
positivity nor invertibility of the level.

Together with the forward theorem in `FullLevelTrivialization`, this
proves `isFull_iff_torsionCoproductMap_isIso` at positive level invertible
on the base. This is a criterion on the actual enumeration map over an
arbitrary scheme, including a nonreduced base. It does not prove openness or representability of a full-level locus,
existence of a full level, an embedding, automorphism faithfulness or
moduli representability.
