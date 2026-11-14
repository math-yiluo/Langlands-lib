# Compatibility of prescribed-torus Levi witnesses on pullback squares

Worker 592.

This derived helper works over arbitrary schemes and retains the explicit
`DynamicRelativeLeviStatement` and `RelativeUnipotentRadicalStatement`
inputs. Both selected witnesses are supplied with prescribed-torus dynamic
presentations. No geometric structure statement is proved here.

`TorusLeviWitness.squareTransport` pulls the actual source group and
inclusion of a witness along one side of a commuting square. It then uses
`Descent.squareComparison` to identify the resulting ambient group with
the iterated pullback along the other side. Naturality of that comparison
for the prescribed commutative group inclusion makes the square required
by witness transport commute. The projection lemmas record that the
source is the actual pulled-back group and the inclusion is its pulled-back
inclusion postcomposed with the ambient comparison.

`TorusLeviWitness.square_range_eq` compares this transported witness with
an independently chosen witness on the other side, after pulling that
witness to the square. Both are Levi subgroups containing the same
prescribed group; uniqueness of the transported witness identifies their
all-test ranges. Composing with the inverse ambient comparison gives the
stated equality in the first iterated ambient pullback.

`EtaleTorusLeviData.overlap_range_eq` specializes the square to every
pairwise fibre product of cover members. These are equalities of subgroup
functors on all test schemes, including nonreduced schemes. The conclusion
provides overlap compatibility. `EtaleTorusLeviData.isMatching` applies
`CoverDescent.isMatching_of_overlap_range_eq` to obtain compatibility on
all relative test schemes and every comparison between them. Effective
descent and the unconditional torus-Levi theorem remain separate obligations.

The provenance is internal: arbitrary-base witness transport, its
uniqueness field, and the published natural comparison for a commuting
pullback square.
