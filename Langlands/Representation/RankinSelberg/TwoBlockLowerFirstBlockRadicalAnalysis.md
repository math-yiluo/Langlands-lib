# Analytic laws for the lower mixed radical tower

This is derived support for JPSS (1983), Section 4.9 equation (2), printed page
416, over every canonical p-adic field and arbitrary positive two-block shape.
It proves the complete radical part of the published linked integration target.
The actual lower mixed and mixed quotient measures are restricted to their zero
determinant slices. Every supplied rectangular additive Haar `μR` is retained,
and the coefficient `c` is exactly its integral-cube mass.

The proposition abbreviation `RadicalIntegrationStatement` records an actual
measurable s-finite kernel, its everywhere representative pushforward law, the
zero-slice composition identity, the nonnegative Tonelli formula, the equivalence
characterizing absolute integrability of every measurable complex function, and
the conditional analytic conclusions for the published total `radicalAverage`.
The theorem `radicalIntegration` proves this proposition for every lower mixed
and mixed quotient measure compatible with the fixed subgroup Haar measures and
the common fixed ambient Haar.

The proof chooses the already constructed `radicalKernel`; its s-finiteness
comes from the published properness and compact-finiteness result. The preceding
radical tower supplies the required composition identity at slice zero. The
integer cube is compact and contains a nonempty open set, so its Haar mass is
strictly positive and finite, as supplied by the published cube-mass lemma.

`radicalAverage_eq_integral_radicalKernel` proves pointwise that the published
unweighted average is integration against this kernel. Quotient induction
exposes the representative formulas, and the measurable fiber pushforward
change of variables identifies the two total Bochner integrals.

The remaining arguments apply the generic scaled-kernel lemmas from
`TwoBlockUnipotentQuotientAnalysis`. The nonnegative identity is the integral
formula for a measurable kernel composed with a measure. Since `0 < c < ∞`,
integrability against `c • νM0` is equivalent to integrability against `νM0`.
The genuine composition integrability theorem then gives exactly almost
everywhere fiber integrability and integrability of the fiberwise norm integral
over `νL0`. This establishes absolute convergence independently of totalized
Bochner equality.

For an integrable function, the composition theorem gives integrability of its
kernel integral and the equality with `c.toReal` times the mixed-slice integral.
The pointwise average identity transfers both conclusions to `radicalAverage`.
Its almost everywhere strong measurability follows from that integrability.
No coefficient or density is built into the average itself.

The kernel packaging and these analytic statements are internal precision of
the source's quotient formula. This pair reuses the proved restricted radical
tower and does not assert the separate first-block disintegration of equation
(8), which is needed to assemble the full linked target.
