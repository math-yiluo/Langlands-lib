# Geometric reciprocity through prescribed closure comparisons

Worker 125. Internal transport infrastructure for Task 4919.

`closureComparisonCorrection` compares the published chosen extension of an
embedding of p-adic fields to algebraic closures with any supplied extension.
Their composite fixes the base field, so it is an element of the actual
absolute Galois group. Both carrier universes remain arbitrary.

`reciprocityUnits_compatible_closure` proves the norm identity for any map of
actual local Weil groups whose projections commute with the supplied closure
comparison. It assumes standalone candidates satisfying the full geometric
reciprocity relations. Projection injectivity identifies that Weil map with
the chosen extension Weil map followed by conjugation by the correction.
Conjugation is trivial on reciprocity, by the published closed-commutator
argument, so the published extension norm identity gives the result. The
field norm uses exactly the algebra structure induced by the input embedding.

These are internal derived constructions from `IntermediateWeil`,
`ExtensionNormReciprocity`, and `WeilTransferReciprocityTower`. In particular,
the companion identity reuses `reciprocityUnits_extensionWeilMap` and
`reciprocityUnits_weilConj`; it makes no unconditional existence or transfer
claim. No additional external source is used.
