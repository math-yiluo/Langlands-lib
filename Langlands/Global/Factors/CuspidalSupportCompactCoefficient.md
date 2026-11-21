# Standard tensors from compact cuspidal block evaluations

The compact covariance of a block evaluation identifies translation by
the ambient block diagonal compact matrix with the product action on
the coefficient tensor. A compact element in one block gives the
corresponding single-slot action. Testing after product-compact
translation separates the coefficients because the cuspidal block
probes have that separation property.

The real comparison applies these probes to the supplied evaluations.
The single-slot comparison transfers the sign equations and the compact
standard slices to the ambient group. The normalized Lie equations
transfer through `CompactJacquetBlockEvaluation`. Vanishing of all
ambient compact probe values implies vanishing of all coefficient
evaluations on compact translates, hence vanishing of the source
vector. These are the inputs to `exists_realStandardTensor_of_compactJacquet`
with the standard module of the ordered block concatenation.

The complex comparison uses the entries of the concatenated character list
indexed by its total rank. The block index formula matches each entry of
the concatenation with the original character in its block. The two
diagonal equations for the complex block probes give the normalized
exponent and the integral weight of each entry. Compact separation and
the normalized block Lie equation then give the complex standard tensor.

This is a derived implication from the actual cuspidal probes in
`CuspidalCoefficientProbes` and the separate compact and Lie covariance
comparisons. It uses the compact-picture route for the local constituent
step of Langlands (1979), Lemma 1, p. 203 (registered PDF p. 198).
