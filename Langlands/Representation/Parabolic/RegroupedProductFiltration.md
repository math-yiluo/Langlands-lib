# Actual full-product filtrations through ordered regrouping

Author: Worker 494.

This internal construction transports a supplied actual filtration in one
factor of a regrouped normalized upper product to an actual invariant-subspace
filtration of the original flat product. It uses the independently proved
`Langlands.Parabolic.orderedProductRegrouping`, preserving its arbitrary ordered
refinement, exact label bijection, factor-rank identities and ambient coordinate
identities. Actual equivalences identify the inner normalized products with
the supplied outer factors `τ`. No regrouping theorem is assumed.

`regroupedProductSlotFiltration` first forms
`normalizedProductSlotFiltration` in the actual outer product. It transports
that filtration along the inverse of
`normalizedProductRegroupingToEquiv`. Its ambient representation is exactly the
original flat product, including all original factors. The membership theorem
identifies each step with the preimage of the corresponding actual outer step
under the forward regrouping equivalence. The original zero and full endpoints
are retained by the published filtration transport construction.

`regroupedProductSlotFiltrationGradedEquiv` identifies each actual quotient of
this full-product filtration with the actual normalized outer replacement
product, given an equivalence at the slot quotient and equivalences at the
other outer factors. The graded map constructor instead permits an arbitrary
intertwiner at the slot quotient. The original outer factors are explicitly
assumed smooth in both comparisons. Replacement factors need not be smooth.
The map's injectivity follows from injectivity of the supplied slot map,
the published tensor-and-induction injectivity theorem, and the equivalence
between the original and transported actual graded quotients.

`exists_injective_regroupedProduct_replacement` starts with an actual injective
intertwiner from an irreducible representation into the original flat product.
It applies the generic finite-filtration embedding theorem to the transported
filtration and composes the selected graded embedding with its injective
replacement map. Replacement carriers, outer representations and slot maps
may all depend on the selected grade. Neither all grades nor their target
representations are assumed irreducible or nonzero.

`exists_injective_regroupedProduct_target` additionally composes the selected
embedding with a supplied actual equivalence from each outer replacement
product to a chosen representation of the full ambient general linear group.
In particular a consumer may supply an actual replacement flat product and
the inverse of its own actual regrouping equivalence. The equivalences required
by this final step remain explicit hypotheses; this module does not construct
segment replacement data or identify those data's products.

All primes, supplied field topologies and natural total ranks are retained.
Field, original factor, outer factor, replacement factor, embedded and final
target carrier universes are independent. Actual induced carriers have the
universe growth already specified by normalized induction. Filtration length
is arbitrary, including zero. In length zero the embedding hypotheses cannot
hold for an irreducible source, consistently with the conclusion indexed by
`Fin 0`. This is not the separate empty-multisegment socle argument.

The provenance is internal composition of the published ordered regrouping
proof, its actual-equivalence adapter, the actual product slot filtration and
its quotient comparisons, equivalence transport of actual filtrations, and
irreducible embedding extraction. No external theorem is asserted here.
The imported regrouping proof closes its comparison inputs through actual
coordinate normalization, induction in stages and the refined
induction/tensor comparison. This module uses no segment analytic
classification, special-head exhaustion, quotient coverage, tempered
uniqueness, square-integrable classification or exhaustion, or regular
exhaustion conclusion. It does not prove individual segment socles, unlinked
commutation, linked reduction, ordered strong socle existence, or the parent
multisegment socle-exhaustion theorem.
