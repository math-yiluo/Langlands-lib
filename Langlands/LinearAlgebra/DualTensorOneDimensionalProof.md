# Dimension one of a full tensor dual

Author: Worker 174.

`Langlands.LinearAlgebra.dualTensorOneDimensional` proves exactly
`Langlands.LinearAlgebra.DualTensorOneDimensionalStatement`, with independent
universes for the field, finite index type, and vector-space carriers. It adds
no hypotheses to that closed proposition.

The proof first translates a nonzero spanning element into `finrank = 1`.
For a full dual of dimension one, positive finite rank supplies finite
generation of the dual; Mathlib's `Module.finite_dual_iff` then supplies finite
generation of the original vector space. The finite-dimensional dual-rank
identity applies at that point. The converse starts with the finite generation
implied by the original space having dimension one.

For tensor products, choose an arbitrary basis in each factor. Mathlib's
indexed tensor basis is indexed by the product of the basis index types.
If the tensor has dimension one, this product index has a unique element.
It gives an element in every factor index; updating one coordinate proves
that index is a singleton. Conversely, singleton bases in the factors give a
singleton tensor basis. This also covers zero factors and empty indexing.

The final theorem combines these equivalences with no finiteness assumption
on the initial vector spaces and no tensor-of-duals identification. It is
internal linear algebra for the eventual Whittaker proof, with no source
transcription or claim to prove the induction comparison.

The helper `nonzero_span_iff_finrank_one` treats arbitrary modules over a
field. `dual_finrank_one_iff` applies the duality step, and
`piTensor_finrank_one_iff` applies the tensor-basis step. The final theorem
rewrites the two nonzero-spanning-functional conditions through these three
equivalences.
