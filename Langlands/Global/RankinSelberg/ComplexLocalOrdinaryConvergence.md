# Absolute convergence of the original complex unequal-rank integral

`ComplexLocalOrdinaryConvergenceStatement` proves absolute convergence of the
original unequal-rank kernel for the two published complex local Whittaker
models on a common right half-plane for each pair of vectors. It uses the
actual quotient measure `D.measure` and the determinant weight of
`complexUnequalIntegrand`.

The representative formula evaluates the kernel on a positive diagonal
times a unitary matrix. Padding the smaller diagonal by ones preserves the
sum of its absolute logarithms, and padding preserves unitarity. The final
logarithm of the padded diagonal is zero, so each positive logarithm of the
smaller diagonal is bounded by the sum of positive simple roots in the
larger rank. The determinant weight has norm
\(\exp((2\operatorname{Re}s-(r-t))\sum_j y_j)\), because the complex
normalized absolute value is the square of the usual modulus.

The proof applies arbitrary simple-root decay to the larger vector and
the fixed growth bound to the smaller vector. The spectral threshold
absorbs both growth exponents and the linear toral density. For each
parameter above that threshold, it chooses the root decay order to control
the positive logarithms. The resulting bound combined with the density
is a constant times \(\exp(-\sum_j|y_j|)\). Continuity of the exact kernel
supplies measurability, and the toral marginal and the Lebesgue integral
of this exponential give integrability on the quotient.

This implements the original unequal-rank convergence argument in
Jacquet 2009, §5.1, p. 32, using the logarithmic form of the majorants in
§3.1, pp. 12–14. The dual rectangular integral and the functional equation
remain separate obligations.
