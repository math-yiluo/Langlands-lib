# Finite actual cocharacter centralizers and reductive neighbourhoods

This internal construction supplies the finite-centralizer assembly step for
openness of the actual reductive geometric identity-component locus. It works
over an arbitrary commutative ring and permits disconnected ambient fibres.
It does not construct the initial relative torus or the centralizers' good
neighbourhoods, and it does not prove the final general openness statement.

`RadicalFreeRootCentralizerData i α` records an actual cocharacter annihilating
`α`, an actual group scheme with its inclusion representing that cocharacter's
centralizer on every test scheme, and triviality of that group's unipotent
radical. The representing inclusion is automatically closed in the affine
ambient group. No canonical choice of cocharacter is required.

Over an algebraically closed field, if the actual closed split torus is
self-centralizing, one such datum for every actual root implies triviality of
the ambient unipotent radical. The proof generalizes the existing
`RankOneCentralizerDetection` argument. For any smooth connected normal
unipotent subgroup, normalized conjugation by the torus decomposes its actual
Lie kernel into weights. The actual inclusion differential carries each of
these weights to the corresponding ambient adjoint weight. A zero weight
vanishes because the torus is its entire centralizer and a torus has trivial
unipotent radical. A nonzero ambient weight is an actual root, so its supplied
annihilating centralizer kills that weight through the existing normal
unipotent-centralizer intersection lemma. Injectivity of the actual inclusion
differential then kills every weight of the subgroup. Its Lie kernel is zero;
the closed unit map to this smooth connected group is an isomorphism by the
existing tangent-surjectivity criterion. Thus the normal subgroup is trivial.
The algebraically closed pseudo-reductive comparison gives connected
reductivity when the ambient group is connected.

For a smooth affine family with a supplied standard split torus,
`geometricExponentRootFinset I G i s` enumerates exactly the actual roots of
the actual geometric identity component at the original base point, in fixed
integer character coordinates. Finiteness uses the split-torus weight
decomposition, finite-dimensionality of the actual Lie kernel and the
character-coordinate equivalence; it does not assume a reductive-group root
system.

`geometricRadicalFreeRootCentralizerData` uses an actual relative fixed-exponent
cocharacter centralizer. If its actual geometric identity component is
reductive and the integer character/cocharacter dot product is zero, that
identity component gives the datum for the original ambient geometric identity
component. The representing inclusion is the previously constructed actual
map between those geometric identity components. Its all-test centralizer
property, including the possibly disconnected ambient fibre comparison, is
inherited from `RelativeCocharacterCentralizer`.

`identityComponentReductiveNeighbourhood_of_rootCentralizers` takes a closed
relative standard torus, self-centralizing at the specified geometric fibre.
For each root in that fibre's finite actual root enumeration, it takes a fixed
integer cocharacter vector annihilating the root and an actual good open
neighbourhood for that relative centralizer. The output is an actual open
neighbourhood for the ambient family, contained in its actual reductive
geometric identity-component locus.

The output open is the intersection of the finitely many centralizer opens,
the open self-centralizing-torus locus and a neighbourhood where the full
actual root profile is constant. It contains the original point. At any point
of this intersection, every actual root corresponds to an integer vector in
the original finite enumeration. The corresponding fixed cocharacter still
annihilates it; its actual geometric centralizer identity component is
reductive by the supplied good neighbourhood. The field detection argument
therefore proves reductivity of the original ambient geometric identity
component at that point.

The provenance is internal: the proof composes the previously implemented
actual radical-detection argument, integral character and cocharacter
coordinates, geometric centralizer comparison, root-profile constancy and
finite intersection of opens. It imposes no characteristic, noetherian or
connected-ambient-fibre restriction. Construction of the supplied centralizer
neighbourhoods and initial relative torus remains part of the general openness
proof.
