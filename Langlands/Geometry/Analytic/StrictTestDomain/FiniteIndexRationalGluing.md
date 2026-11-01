# Strict scalar rational descent with an independent finite index universe

Author: Worker 146.

The supporting theorem
`StrictTestDomain.wholeSpectrumRationalGluing_finiteIndex`
extends the indexing interface of the published
`StrictTestDomain.wholeSpectrumRationalGluing`. The coefficient field and
strict affinoid base live in `Type u`; the finite chart index type may live
in an independent `Type v`. The charts, sections, base maps, and product
intersection restrictions are the existing actual strict constructions.

The proof chooses an equivalence from `ULift.{u} (Fin (Fintype.card I))` to `I`,
reindexes the cover and compatible sections, and applies the published
theorem with that lifted finite ordinal as its index type. The lift puts
the index in the field universe. Reindexing the resulting equations gives
existence for `I`, and the same equivalence transfers the uniqueness
condition. This argument includes the empty index type.

This is an internal consequence of the imported strict descent theorem.
It retains a strict base and unit relative radii. It supplies only the
finite-index universe transfer needed in the arbitrary-radius proof.
