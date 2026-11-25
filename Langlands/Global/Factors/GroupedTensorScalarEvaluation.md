# Scalar evaluation of grouped tensors

`groupedPure` places one ordinary complex pure tensor and one nested pure tensor into a binary tensor. The block index `I`, the outer index `J`, and their coefficient spaces can live in separate universes. The definition works for arbitrary index types.

`groupedProductCovariance` compares two scalar linear evaluations whose values on `groupedPure` factor as products over the finite block index `I`, supplied with `Fintype I`. It also assumes `Finite J`, which lets pure tensors in the nested factors determine the outer tensor evaluation. The proof applies the specified covariance of every scalar factor to identify the two products, then extends the equality by tensor extensionality. The two specializations keep the same finiteness assumptions and apply operators in just one of the two families.

This is an internal tensor argument for the finite and infinite Levi coefficient comparisons toward `CuspidalIsobaricAutomorphyStatement` (automorphy of isobaric sums of cuspidal representations at every place, Getz–Hahn Theorem 10.7.5). Flath (1979), §2, pp. 180–181 (PDF 176–177), provides the tensor product setting. The Lean proof uses the Library's maps and extensionality for indexed tensors.
