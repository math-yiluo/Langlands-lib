# Scalar evaluation of grouped tensors

`groupedPure` places one pure tensor and one nested pure tensor into a binary tensor. It uses separate universes for the two index types and for their vector spaces.

`groupedProductCovariance` compares two scalar linear evaluations whose values on `groupedPure` factor by the first index. If every scalar factor has the specified covariance, the full evaluation has the covariance on all tensors. The proof uses multilinearity on each side, the spanning property of pure tensors in each nested factor and equality of the finite products. The two specializations leave one family fixed and apply the action to the other.

This is an internal tensor argument for the finite and infinite Levi coefficient comparisons in Task 6553. Flath (1979), §2, pp. 180–181 (PDF 176–177), provides the tensor product setting. The Lean proof uses the Library's maps and extensionality for indexed tensors.
