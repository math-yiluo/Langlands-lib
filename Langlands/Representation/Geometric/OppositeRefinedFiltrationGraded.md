# Jacquet descriptions of the transported opposite grades

Worker 514 supplies an internal exactness adapter for the actual filtration
constructed in `OppositeRefinedFiltration`. For a smooth representation `A`
of `GL_n(F)`, a block shape `B`, a refinement `S`, and any supplied filtration
of the actual normalized upper Jacquet module along `B.reverse`, it identifies
each grade of the constructed composed opposite filtration with the actual
normalized refined opposite Jacquet module of the corresponding original
grade pulled back along `leviReverseEquiv B`. The filtration index is unchanged.
The field, original carrier, and an optional identified grade carrier have
independent universes.

`continuous_leviReverseEquiv` proves continuity of block relabelling using
continuity of every coordinate projection in the finite product topology.
`isSmooth_oppositeJacquet` first uses the published smoothness of the normalized
upper Jacquet module along the reversed shape, pulls it back along this
continuous homomorphism, then transfers smoothness through the published actual
normalized reversal equivalence.

`composedOppositeFiltrationOfReverseGradeJacquetEquiv` composes three actual
representation equivalences. It reverses the final filtration transport,
uses the refined clause of the proved
`Parabolic.normalizedOppositeJacquetFiltrationGraded` to identify the intermediate
image grade, and applies `normalizedRefinedOppositeJacquetCongr` to the inverse
grade equivalence of the reversal transport. The smoothness input needed by
the exactness theorem is derived from smoothness of `A`.

`composedOppositeFiltrationOfReverseGradeCongr` further transports any supplied
actual equivalence from the original grade to a representation of the reversed
Levi. It pulls this equivalence back through block relabelling and applies the
same normalized refined opposite Jacquet congruence. No smoothness assumption
on this identified grade is needed.

The provenance is internal composition of the published smoothness transfer,
normalized reversal, filtration transport, opposite quotient exactness and
quotient congruence results. The quotient actions keep their actual
normalization. These adapters do not construct a geometric filtration or
identify a Weyl piece, its coarse contribution, a responsible branch or its
continuation. They supply no proof of the supported branch obstruction.
