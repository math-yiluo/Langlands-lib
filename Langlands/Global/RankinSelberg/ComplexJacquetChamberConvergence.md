# Absolute convergence of the complex open-cell Jacquet integral

`complexJacquetOpenCellConvergence` proves absolute integrability of
\(u\mapsto f(w_nug)\) on the upper unipotent group in the strict
upper-Borel chamber. The real parts of adjacent inducing exponents
strictly decrease. The measure is the product of the supplied scalar
Haar measure in the strictly upper entries. The result applies to every
group argument \(g\). Multiplying the integrand by the unitary Whittaker
character preserves its absolute integrability.

`sphericalMajorant` is the positive radial section for the real parts of
the inducing exponents. Its restriction to the unitary group is one.
Iwasawa decomposition separates the upper-Borel factor from the translate
on the unitary group. The norms of the original Borel factor and the
radial factor agree. A compact bound for the translate therefore yields
`norm_mul_le_sphericalMajorant`. This part uses continuity and the Borel
transformation law, as recorded in
`integrable_openCell_of_borelCovariance`.

The proof integrates the positive section at the transpose of the
unipotent argument by induction on the rank. Transposing the ordered
upper-left and last-column product gives a last-row Jacquet chart
followed by the embedded transposed smaller block. The last-row
convergence theorem makes the inner integral finite. Positivity
identifies its norm with the integral of the norms. The proved partial
Jacquet integral preserves compact finiteness and shifts all retained
exponents by the same amount, so the induction applies to the result.
The supplied column measure is a finite scalar multiple of the
Lebesgue measure in the partial Jacquet theorem. The antidiagonal
reflection preserves the entry product and converts the transpose
estimate to \(w_nu\).

This is the chamber convergence used in Jacquet, *Archimedean
Rankin–Selberg integrals* (2009), §7.2, (7.3), p. 47. The upper-Borel
convention reverses the order of the exponents in the displayed chamber.
