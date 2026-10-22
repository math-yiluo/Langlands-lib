# The block-label map of a coordinate permutation

`Langlands.CuspidalSupport.blockMap B C w i` is the block of `C` containing
`w (B.index i ⟨0, B.positive i⟩)`. Positivity of the source block makes its
first coordinate available. The definition needs only two block shapes of
the same natural rank and a coordinate permutation; it assumes no field or
Levi-conjugation hypothesis.

This is the identical definition shared by the independently accepted
cuspidal tensor association, minimal Weyl transport and total conjugating
count proofs. It was extracted here during integration, retaining the name
`blockMap` from the latter two and replacing the tensor proof's `blockImage`.
The consumer modules prove the relevant compatibility and bijectivity lemmas
under their own conjugation hypotheses. No additional result is asserted here.
