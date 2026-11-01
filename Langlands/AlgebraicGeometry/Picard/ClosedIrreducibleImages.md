# Closed images of closed irreducible subsets

`Langlands.AlgebraicGeometry.ClosedIrreducibleImages p` requires that the
image of every closed irreducible subset of the source scheme is closed in
the base scheme. It uses the actual underlying map of `p`, with no change
of scheme or quotient of subsets. Mathlib's `IsIrreducible` includes
nonemptiness.

This is exactly the topological condition in the last assertion of
Grothendieck and Dieudonne, *EGA IV*, fourth part (1967), Proposition
18.10.19, printed p.167 (zero-based PDF page166). The registered original
is `grothendieck-dieudonne-ega-iv4-1967`. Its original List3 errata was
checked for corrections to 18.10.19 and 18.10.20; none was found. No
source-specific project errata note was present in the checked locations.
The definition isolates one hypothesis of that proposition; it does not
state its rational-section extension conclusion.

`closedIrreducibleImages_of_isClosedMap` proves the condition for any
closed underlying map by applying that map's closed-image property to the
given closed subset. The irreducibility assumption is unnecessary in this
special case. `closedIrreducibleImages_of_universallyClosed` obtains the
closed-map hypothesis from Mathlib's `Scheme.Hom.isClosedMap`. These two
proofs are internal consequences of existing Mathlib definitions.

The condition is asserted for the displayed map on the displayed base.
It does not require closedness after every base change. In particular,
this module does not define the full essentially proper condition of
EGA IV 18.10.20, which has further hypotheses and a universal condition
over locally noetherian bases. There is no finiteness, separation or
noetherianity assumption here, and the universe is arbitrary.
