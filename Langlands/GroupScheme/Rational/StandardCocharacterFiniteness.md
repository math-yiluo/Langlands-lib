# Finiteness from standard-cocharacter existence

This internal auxiliary development proves a converse ingredient needed by
the standard-Levi annihilator reduction. It retains the actual
character-valued simple roots and their published definition.

`IsSplitTorus.finite_characterLattice` transports the finite generation of
the integer module of coordinate tuples along a chosen split-torus
isomorphism and the published character-lattice equivalences.

`linearIndependent_simpleRelativeRoots_of_standardCocharacter_exists`
assumes that every subset of the actual simple-root set admits a standard
cocharacter. For each simple root `α`, take a standard cocharacter for the
complement of `{α}` in that set. Pairing with this cocharacter vanishes on
every other simple root and is a strictly positive integer on `α`.
Applying that integer linear functional to any finite linear relation
shows that the coefficient of `α` is zero. This proves integer linear
independence without presupposing finiteness.

`finite_simpleRelativeRoots_of_standardCocharacter_exists` combines that
independence with finite generation of the split character lattice. A
linearly independent family in this finite integer module is finite.
`simpleRelativeRootsFintypeOfStandardCocharacterExists` constructs a finite
enumeration of the actual simple roots under those same hypotheses.

The existence premise remains explicit. This file does not prove standard
cocharacter existence for general reductive groups, and it does not assert
the general relative-root-system comparison. Its proof uses only the
published lattice equivalences, the standard-cocharacter inequalities, and
general module results from Mathlib.
