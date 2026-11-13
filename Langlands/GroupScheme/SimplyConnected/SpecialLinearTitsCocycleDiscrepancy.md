# The coordinate Galois discrepancy and its torus action

This internal derived unit specializes the actual torus-compatible Galois
discrepancy to `SpecialLinearTitsCocycle.Presentation`. It supplies an
automorphism of the split special linear model over the stage field and an
automorphism of its fixed coordinate diagonal torus. It does not classify that
automorphism by matrices or identify its based root action with the star action.

`diagonalTorus_baseChange` proves that the actual `FinSucc.diagonalTorus`
inclusion commutes with the canonical special linear and split torus model
comparisons. Its proof tests equality on every relative scheme, applies the
published special linear point equivalence, and uses the split torus point
comparison to identify all diagonal entries.

For a presentation `p`, `coordinatePinning` names the fixed coordinate pinning
already retained by `p.coordinate`. `baseChangeTorusIso` composes the split torus
base-change model comparison with the pinned torus isomorphism of the
presentation. The theorem `baseChange_square` composes the diagonal model square
with the retained pinned inclusion square, so it compares the actual
base-changed ground-field torus inclusions.

`discrepancyIso p sigma` conjugates `GaloisDiscrepancy.groupIso p.baseChangeIso
sigma` by the special linear model comparison. Its diagrammatic order is the
inverse model comparison, the discrepancy, and then the forward model
comparison. `discrepancyTorusIso` uses the same order with the split torus model
comparison and `GaloisDiscrepancy.torusIso p.baseChangeTorusIso sigma`.
The theorem `discrepancy_square` proves that these automorphisms preserve the
actual coordinate torus inclusion. It first applies the generic discrepancy
square to `baseChange_square`, then transports it across the two model
comparisons. The private categorical lemma proves this transport by cancellation
and the two original squares; the private commutative-group helper merely
forgets additive notation on homomorphisms.

Finally, `discrepancyTorusIso_character` identifies pullback of every coordinate
character by the discrepancy with the ordinary character Galois action of
`sigma` inverse, conjugated by the actual coordinate pinned torus isomorphism.
The proof applies the generic inverse-Galois character formula to the split
ground-field torus, then cancels the model comparisons. The inverse is part of
the specified discrepancy convention.

All constructions are polymorphic in the ambient universe and retain the
original `TitsIndexData`, its finite stage and its coordinate pinning. They impose
no characteristic or positive-rank restriction. The provenance is entirely
internal: composition of the published presentation, canonical model
comparisons, and the generic torus-compatible discrepancy helper. No new
external result or downstream classification theorem is used.
