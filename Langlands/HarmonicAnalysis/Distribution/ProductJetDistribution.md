# The finite transverse jet formula for a supported distribution

Let \(T\) be a distribution on \(U\times V\) vanishing away from
\(U\times\{0\}\), where the transverse space \(W\) is finite-dimensional.
Fix a compact product \(K\times L\subset U\times V\) and a cutoff
\(\chi\) supported in \(L\) that equals one near zero. The order-\(i\)
coefficient functional applies \(T\) to the continuous single-order
extension of a test on \(U\) with multilinear values.

For tests supported in \(K\times L\), the evaluation of \(T\) is the
sum of these functionals on the transverse derivatives through the
distribution order on \(K\times L\). The proof subtracts the sum of
single-order extensions of the extracted derivatives. Each extracted
derivative is supported in \(K\), and each extension remains supported
in \(K\times L\). By symmetry of the extracted coefficients and the
single-order extension identities, the remainder has zero transverse
derivatives through the compact order. The flat-test theorem
`distribution_eq_zero_of_transverseProductJet` of `FlatProductJets`
then gives zero evaluation on the remainder.

This internal formula applies to each fixed compact product. Its order
is supplied by the distribution bound on that product.
