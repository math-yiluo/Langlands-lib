# Pointwise Fourier vanishing on complex rows

`ComplexRowFourier.eq_zero_of_character_integrals` concerns a function
\(\Psi\) on the space of complex rows \(\mathbb C^m\), integrable for the
product Lebesgue measure and continuous at a point \(\eta_0\). If

\[
\int_{\mathbb C^m} \psi_a\Bigl(\sum_i \eta_i x_i\Bigr)\,\Psi(\eta)\,d\eta = 0
\quad\text{for every } x\in\mathbb C^m,
\]

where \(\psi_a\) is `complexScaledCharacter a`, \(z\mapsto
e^{2\pi i\,\mathrm{Tr}_{\mathbb C/\mathbb R}(az)}\), then \(\Psi(\eta_0)=0\).

## Proof

The row space is identified with the real inner product space
`EuclideanSpace ℂ (Fin m)` by the coordinate equivalence. The image of its
volume is an additive Haar measure on \(\mathbb C^m\), hence a nonzero multiple
of the product Lebesgue measure. The composite of \(\Psi\) with the coordinate
map is therefore integrable and continuous at the corresponding point.

For a frequency \(w\) put \(x_i=-\overline{w_i}/(2a)\). Then
\(\mathrm{Tr}(a\sum_i\eta_i x_i)=-\sum_i\mathrm{Re}(\overline{\eta_i}w_i)
=-\langle\eta,w\rangle_{\mathbb R}\), so the Mathlib Fourier transform of the
composite at \(w\) is a multiple of one of the vanishing integrals. The Fourier
transform is therefore zero, and Mathlib's Fourier inversion theorem at a point
of continuity (`MeasureTheory.Integrable.fourierInv_fourier_eq`) gives the value
zero at \(\eta_0\).

This lemma is the pointwise inversion step of the implemented descent in
`ComplexUnequalOrdinaryDescent`, applied there to the last-row density of an
ordinary unequal-rank integrand. The last-row character calculation and the
multiplication of a Whittaker function by a Schwartz function of the last row
that this step replaces are in H. Jacquet, *Archimedean Rankin–Selberg integrals*
(2009), §6.2, Propositions 6.1–6.2, author pp. 41–42 (registered source
`jacquet-2009-archimedean-rankin-selberg`). The lemma itself is standard harmonic
analysis on \(\mathbb C^m\).
