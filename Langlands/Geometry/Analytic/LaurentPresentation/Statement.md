# Spectrum identification target for a Laurent presentation

Author: Worker 36.

`Langlands.Analytic.LaurentPresentation.SpectrumIdentificationStatement`
concerns the actual quotient and bounded base map in
`LaurentPresentation.Definitions`. K is a complete ultrametric normed
field. The base is an arbitrary finite Tate quotient by closure(span S),
and the upper and lower functions are arbitrary series representatives.
The quotient uses common denominator G = product_j g_j and numerators
f_i G, G_j = product_{k ≠ j} g_k, and 1.

The five conclusions are:

- Those denominator and numerator images generate the unit ideal in the
  base, with no hypothesis on the selected functions.
- Their rational inequality locus equals the Laurent locus x(f_i) ≤ 1
  and 1 ≤ x(g_j).
- The spectrum map induced by the bounded base map has exactly that
  Laurent locus as its image.
- That spectrum map is a closed embedding for the pointwise spectrum
  topologies.
- The Laurent locus is compact.

There is no assumed nonempty spectrum, point lift, invertible denominator,
or domain-factorization object. Either tuple or the original variable
list may be empty. The statement permits zero quotients and empty loci.
It imposes no nontrivial-valuation hypothesis.

The source context is Berkovich's Trieste 2009 lectures,
Exercise 2.2.2(i),(iii), p.9, and Fact 2.2.3(i), p.10. This is a
derived unit-radius presentation-level formulation. The source's
Laurent inequalities and rationality assertion motivate the explicit
common-denominator construction; the Lean target concerns that
constructed quotient and its spectrum. It does not identify it with
the source's displayed relative-series Laurent quotient, nor assert
the full analytic-domain universal property in Definition 2.2.1.
General radii and presentation independence are also separate.
Compactness is the elementary consequence of closed seminorm
inequalities in the compact base spectrum.

Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
