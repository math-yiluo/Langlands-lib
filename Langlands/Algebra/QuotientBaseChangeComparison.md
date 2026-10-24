# Proof of the canonical quotient base-change comparison

`Langlands.Algebra.quotientBaseChangeComparison` proves exactly
`Langlands.Algebra.QuotientBaseChangeComparisonStatement`, with its three
independent universe parameters and no additional hypotheses.

Let R, B and T be the rings in the statement, and let I be contained in J with
equal extended ideals in `B tensor_R T`. The proof uses
`Algebra.TensorProduct.quotientTensorEquiv` to identify each base-changed quotient
with the quotient of `B tensor_R T` by its extended ideal. It composes the first
identification, `Ideal.quotientEquivAlgOfEq` for the assumed ideal equality, and
the inverse of the second identification to obtain an R-algebra equivalence
between the two base-changed quotients.

`Algebra.TensorProduct.ext'` reduces equality with the canonical tensor map to
pure tensors. Surjectivity of the quotient map writes the first tensor factor
as the class of some b in B. The pure-tensor formulas for the quotient
equivalences and the canonical factor map then simplify both sides to the same
class tensor t. Thus the specified algebra tensor map, not just an abstract map
between its source and target, is bijective.

For the second assertion, `LinearMap.lTensor_bij_iff_rTensor_bij` expresses the
invariance of bijectivity under tensor symmetry. The right-tensor linear map is
the underlying function of the algebra tensor map just proved bijective, so the
first assertion supplies the needed premise directly.

This is the elementary quotient-fibre comparison used in the source route of
Stacks tag 05UV, generalized in the target statement to arbitrary base change.
The proof uses Mathlib's quotient and tensor equivalences. It proves neither the
local injectivity-lifting criterion nor the final fibrewise flatness criterion;
those use this comparison as a separate prerequisite. Source provenance and
its specialization to residue fields are recorded in the paired statement
Markdown.
