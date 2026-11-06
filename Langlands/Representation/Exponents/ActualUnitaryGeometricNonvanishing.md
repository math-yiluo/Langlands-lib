# Nonzero maps and actual unitary geometric pieces

This derived supporting construction implements the nonzero-piece extraction
and its first nonvanishing consequence in Renard,
*Représentations des groupes réductifs p-adiques*, edition dated
9 July 2026, VII.2.6 theorem, uniqueness proof, printed p.231 / PDF p.237.
The source applies the tempered geometric lemma to a nonzero map out of a
unitary Jacquet module. It obtains a nonzero map from one induced unitary
piece and concludes that the inner unitary Jacquet summand is nonzero.

`D.NonzeroUnitaryPieceMap ha' σ τ` stores an actual intertwiner
from `D.unitaryPieceRep ha' σ` to the original target representation `τ`,
together with its nonzeroness. All group schemes, parabolic, Levi and
radical maps and witnesses belong to the actual supplied
`GeometricLemmaIntersectionDatum D`. The split component `ha'`
is that of the inner Jacquet Levi, as in the published unitary piece.

`NonzeroUnitaryPieceMap.unitaryJacquetPart_ne_bot` proves that the
inner unitary Jacquet summand of `σ` is nonzero. If that subrepresentation
were bottom, every value of every function in the induced piece would be
zero. Extensionality of the smooth induced functions then makes every
source vector zero, so every linear map from the piece vanishes,
contradicting the stored nonzero map. This proof uses the actual
function model and needs no intersection fullness, admissibility,
irreducibility, temperedness or quotient compactness.

`nonzeroUnitaryPieceMapOfFiltration` constructs an index and this
nonzero-map data from a supplied finite object filtration, a permutation,
the supplied equivalences from its actual graded quotients to the
unitary pieces, and a nonzero map out of the filtered representation.
The published `ObjectRepFiltration.exists_mapFromGraded_ne_zero`
selects the first step on which the original map does not vanish and
descends through its preceding step. Precomposition with the inverse
graded-piece equivalence gives the required piece map. Evaluating a
putative zero equality at the forward equivalence proves it remains
nonzero. The index is transported by the exact supplied permutation.
The construction handles arbitrary finite lengths, including zero:
a nonzero map out of a zero-length filtered object is impossible.

The field universe and both original representation-carrier universes
are independent. The filtered representation has the carrier universe
`max u v`, as required by the published actual unitary pieces.
The nonarchimedean local-field hypotheses, canonical ambient topology,
Levi topologies, and ambient local-compactness and nonarchimedean
instances are those of that definition.

The finite filtration and its graded equivalences are inputs here.
This file does not prove VII.2.5, construct geometric intersection data,
or derive intersection fullness. The nonzero inner summand is the input
to the source's subsequent application of VII.2.4; that criterion and
the remaining uniqueness argument stay separate obligations.
