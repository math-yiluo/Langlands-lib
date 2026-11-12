# Concatenating products of supplied Zelevinsky socles

This internal construction supplies the actual embedding used in the proof of
Zelevinsky 1980, Proposition 8.5. Its mathematical inputs are the published
`SegmentProductDatum.concatenate`, its ordered regrouping equivalence, and
injectivity of normalized induction on blockwise injective maps. It introduces
no new representation theoretic assertion.

For an outer block shape `B` and actual inner data `d i`,
`concatenate_multisegment` identifies the multisegment of the concatenated datum
with the sum of the inner multisegments, including all multiplicities. Its proof
uses the published equality of segment lists, flattening a list of lists, and
finite summation.

`concatenate_isPrecedenceOrdered` assumes each inner datum is ordered and every
pair of segments belonging to distinct outer factors is unlinked. Pairwise
ordering of each inner list and the implication from precedence to linkage give
pairwise ordering of the flattened list.

`socleProductEmbedding` takes supplied strong Zelevinsky socles `π i` of the
inner data and returns an actual injective intertwiner from their normalized
product into the standard product for the concatenated datum. Choose the
injection of each socle, apply normalized product induction, and compose with
the published concatenation equivalence. The definition retains injectivity
as part of its result. It requires no cross nonlinkage; that hypothesis is used
only by the ordering lemma.

All statements retain independent field and carrier universes. There is no
positivity premise on total rank or number of outer factors, so empty outer
products on `GL₀` are included. This module alone does not prove the product
irreducible.
