# Étale-local dynamic presentation of the given Borel pair

Worker 608 and Worker 653.

This module implements the full `RelativeBorelDynamicPresentationStatement`
for every universe and the original arbitrary-base input data. It uses no
Lie-containment or opposite-Borel existence assumption.

Take the relative torus's étale splitting cover. On each chart, the original
reductive group, torus inclusion, maximality, relative Borel and all-test
containment pull back. The residue-cocharacter classification and extension
give a global cocharacter of that split torus for each chart point. Its
positive parabolic and centralizer residue equalities persist on a common
open neighbourhood; the negative-Borel adapter supplies the actual closed
opposite dynamic Borel there.

Bind those small neighbourhood covers to the splitting cover. Each point
neighbourhood contains its index point in its image, so both cover levels and
their composite are jointly surjective. The composite cover remains étale.
`borelDynamicCompositePresentation` transports the cocharacter and all three
certificates from the iterated pullbacks to the actual direct pullbacks of the
original group and torus. The resulting data are exactly the clauses of the
published local-presentation statement.

This implements the local construction isolated from Conrad,
*Reductive group schemes* (2014), Proposition 5.2.3 and the proof of
Proposition 5.2.12. The arbitrary-base opposite Borel target still requires
global descent and uniqueness; its existing reduction retains the separate
Lie-containment-spreading input.
