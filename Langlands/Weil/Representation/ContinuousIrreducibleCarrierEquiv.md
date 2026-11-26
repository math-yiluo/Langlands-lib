# Carrier universes of continuous irreducible representation classes

`FiniteRepresentation.continuousIrreducibleCarrierEquiv` identifies the
rank-\(n\) continuous irreducible complex representation classes of a fixed
topological group in any two carrier universes. The class spaces use the
genuine isomorphism relation on representations, with the usual topology on
finite-dimensional complex endomorphisms for the continuity predicate.

For each source representative, `FiniteRepresentation.transport` conjugates
the action to an `ULift` of its finite-dimensional coordinate space.
`coordinatesEquiv` is the intertwiner from that copy to the original.
Continuity, irreducibility and dimension pass along this equivalence. To
descend to classes, the construction composes a source intertwiner with the
coordinate equivalences at its two ends. The composite of two carrier changes
has an intertwiner to the starting representation, so interchanging the
carrier levels gives an inverse on the quotient.

`continuousIrreducibleCarrierEquiv_rep_iff` characterizes the image of a class
by the existence of an actual complex-linear intertwiner between any source
representative and a proposed target representative.
`continuousIrreducibleCarrierEquiv_twist` uses this criterion and the fact that
the same intertwiner works after twisting both actions by a common continuous
character.

For the local Weil group, these classes are the source of Henniart's
numerical correspondence. See Guy Henniart, *La conjecture de Langlands locale
numérique pour GL(n)*, Ann. Sci. Éc. Norm. Sup. (4) 21 (1988), §§1.1–1.2,
pp. 497–498, for the parameter classes and their character twists
(`henniart-1988-numerical`,
SHA-256 `3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`).
The carrier comparison follows from the finite-dimensional coordinate model
and the isomorphism invariance of the class predicates.
