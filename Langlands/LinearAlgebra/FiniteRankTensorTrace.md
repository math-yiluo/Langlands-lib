# Trace on a finite tensor product of finite-rank maps

`Langlands.FiniteRankEnd.piTensorMap` takes a finite family of complex
finite-rank endomorphisms `T i` and returns a finite-rank endomorphism on the
finite tensor product of the carriers. `piTensorMap_val` identifies its
underlying endomorphism with the existing `PiTensorProduct.map` of the family.
Neither the carriers nor their tensor product are assumed finite-dimensional.
`trace_piTensorMap` proves that its finite-rank trace is the product of the
component finite-rank traces.

The construction factors each map through its finite-dimensional range. The
finite tensor product of those ranges is finite-dimensional, so the tensor of
the range restrictions followed by the tensor of the inclusions gives a
`FiniteRankEnd.ofFactorization`. Its trace is the ordinary trace of the reverse
composition on that intermediate space. `PiTensorProduct.map_comp` identifies
the reverse composition with the tensor of the individual range endomorphisms.

The supporting theorem `Langlands.trace_map_piTensorProduct` is the
finite-dimensional version over any field. In the product basis, each diagonal
matrix entry of the tensor endomorphism is the product of the corresponding
entries for its factors. Summing over all tuples of basis indices factors into
a product of sums by `Fintype.prod_sum`. The component sums are precisely the
component traces. This uses the same product-basis computation as the Library's
`FiniteRep.character_externalRep`, here for arbitrary linear endomorphisms.

This internal algebraic lemma is used for the tensor character calculation on
Levi products in the proof route of Henniart–Lemaire II.4.5. It does not yet
compare integrated actions, character distributions, or their local values.
