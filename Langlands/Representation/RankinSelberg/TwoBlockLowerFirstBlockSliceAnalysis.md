# Analytic laws conditional on the lower first-block slice tower

This module is derived analytic support for Jacquet–Piatetski-Shapiro–Shalika,
*Rankin–Selberg Convolutions* (1983), Section 4.9, equation (8), printed page 418,
registered as `jpss-1983-rankin-selberg`. The exact geometric slice tower is an
explicit premise of its theorem; this module does not prove that tower.

`FirstBlockSliceIntegrationStatement` packages every first-block conclusion for
one integer slice `k` over the exact zero slice of the lower mixed quotient.
The density is `d = ENNReal.ofReal (q ^ (-(k * (m 1 + 1))))`, and its determinant
formula has the positive exponent `m 1 + 1`. The kernel has the actual
representative pushforward law from the small `k` slice. The package includes
its s-finiteness, `d • (κA composed νL0) = νMinusk`, the nonnegative Tonelli law,
the genuine absolute-integrability equivalence, and almost everywhere strong
measurability, outer integrability and the Bochner law for the published
unweighted `firstBlockAverage`. No rectangular cube coefficient occurs.

The theorem `firstBlockSliceIntegration_of_comp` assumes the exact displayed
measure identity for the actual `firstBlockKernel`. It allows arbitrary outer
and lower quotient measures; the small measure is s-finite, finite on compact
sets, and right invariant under the small norm-one subgroup. The fixed Haar
compatibilities that establish this premise belong to the separate geometric
tower. The density theorem supplies positivity, finiteness and identification.
The published compact-preimage argument supplies s-finiteness of the actual
kernel. Quotient induction, its everywhere representative law and the Bochner
pushforward formula identify the actual average with its kernel integral.

Scalar-measure linearity and the measure bind Tonelli theorem give the
nonnegative identity. Since the density is positive and finite, multiplying a
measure by it preserves integrability. The measure composition integrability
theorem then proves the equivalence with almost everywhere fiber integrability
and integrability of the fiber norm integral. For an integrable function, its
integrability against the composed measure yields outer integrability of the
kernel integral and hence almost everywhere strong measurability. The Bochner
composition theorem and scalar-measure formula give the stated integral
identity. Absolute integrability is established independently of the equality
of totalized Bochner integrals.
