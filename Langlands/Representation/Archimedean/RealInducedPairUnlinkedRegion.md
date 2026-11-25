# Nonlinked arithmetic with one zero induction weight

This module connects the positive linked-gap index with the
concrete unlinkedness hypothesis of the single-zero exchange. It proves the
single-zero filtration throughout the region without a positive linked index;
it retains exactly one zero weight and the strict ascending exponent order.
It does not claim the full `RealInducedInducedFiltrationStatement`.

`unlinked_iff` assumes at least one weight is nonzero. For two nonzero weights
it applies `RealInducedSwapArithmetic.unlinked_iff`. If one weight is zero,
its Mœglin data consist of two characters with the same exponent and opposite
parities. The mixed character/discrete-series linking condition does not depend
on the character parity, so both conditions coincide. Their half-weight
threshold is the absolute difference of the original absolute weights divided
by two, as for two nonzero weights.

`unlinked_iff_of_order` removes the reverse linking branch by taking real parts:
under descending order that difference is nonpositive, while the linking value
is positive. `unlinked_reverse_iff_no_linked` reverses the pair and uses the
invariance of the absolute integer weight difference under swapping the inputs.
Replacing a positive natural number by its predecessor identifies the forbidden
gap with `RealInducedPairLinkedReplacement.IsLinkedAt d e k`. No strict
half-weight-gap lower bound is needed for this equivalence.

`filtration_of_no_linked` applies that equivalence and the proved
`RealInducedPairSingleZero.filtration`. The proposition
`RealInducedPairSingleZeroNonlinkedFiltrationStatement` records its exact scope;
`realInducedPairSingleZeroNonlinkedFiltration` proves it.

The provenance is internal: the definitions of `MoeglinDatum.IsLinked`,
`realBlockMoeglinData`, `AreRealBlocksUnlinked` and `IsLinkedAt`, the published
nonzero-weight arithmetic, and the single-zero exchange and filtration. No
irreducibility theorem, classification premise or external source is used.
