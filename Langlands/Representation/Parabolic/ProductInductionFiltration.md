# Actual slot filtrations in normalized block-product induction

This internal adapter combines the supplied external tensor slot filtration
with actual normalized parabolic induction from the standard upper block
parabolic. It supports the independent multisegment socle argument without
asserting any segment classification, linked-segment filtration, or exhaustion
result.

For a block shape `B`, block representations `ρ`, a slot `j`, and a supplied
finite filtration `s` of `ρ j`,
`Langlands.Parabolic.normalizedProductSlotFiltration` is an actual filtration
of `T.normalizedProductInduced B ρ`. First
`FiniteTensor.externalSlotFiltration` constructs invariant tensor subspaces
from the original factor filtration. Then `normalizedInductionFiltration`
requires values of the actual induced functions to lie in those subspaces.
The construction itself does not require smooth block factors or simple
graded pieces.

`normalizedProductSlotFiltrationGradedEquivOfFamily` identifies a full-product
graded quotient with the normalized product of a replacement family `σ`,
given equivalences of all complementary factors and an equivalence of the
actual slot quotient with `σ j`. Its proof first identifies the induced
filtration quotient with induction of the external quotient, using smoothness
of the original block factors. It then induces the external quotient
equivalence. Both endpoints use the supplied block shape and its original
coordinate actions.

`normalizedProductSlotFiltrationGradedMap` uses the same induced quotient
comparison and then induces the external quotient map, when the slot quotient
is supplied with an intertwiner into `σ j`. The theorem
`normalizedProductSlotFiltrationGradedMap_injective` proves that this map is
injective if the supplied slot map is injective: external tensor lifting
preserves that injection, normalized induction preserves it pointwise, and the
quotient comparison is an equivalence.

`exists_injective_normalizedProduct_replacement` allows a replacement family
whose carriers depend on both the grade and the block. Given an embedding of
an irreducible representation into the original product and injective slot
quotient maps for every grade, it produces an embedding into one actual
replacement product. The proof applies
`ObjectRepFiltration.exists_injective_graded` to the supplied full-product
filtration and composes the selected map with its injective replacement map.

The quotient comparisons and replacement selection require smooth original
block factors. The replacement factors have no separate smoothness premise.
All coefficient representations are complex, the supplied p-adic field and
topological data are arbitrary, and the field, original factor, replacement
factor, and embedded representation carrier universes remain independent.
Filtration length is unrestricted, including zero; any assertion of a
selected grade still requires the stated irreducible embedding.

Provenance is internal assembly of the published modules
`Tensor.ExternalFiltration`, `Parabolic.InductionFiltration`,
`Filtration.IrreducibleEmbedding`, `Induction.BlockFactors`, and
`Induction.Equivalences`. No external mathematical theorem is asserted here.
The module does not change block shapes or ranks; those operations belong to
the separate ordered-product regrouping comparison.
