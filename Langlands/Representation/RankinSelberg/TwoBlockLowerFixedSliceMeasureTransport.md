# Measures and slice transport for the Section 4.7 lower quotient

Author: Worker 1191.

This internal helper for fixed-slice convergence defines `lowerMeasure` to be exactly
`Measure.map (lowerToStandard h F.Carrier).symm νN`. All topologies are the canonical
p-adic ones; the measurable structures may be any Borel structures for these topologies.
There is no additional scale or independently selected lower Haar measure.

The published lower-to-standard homeomorphism identifies the lower determinant slice
with the standard slice. `lowerMeasure_restrict` applies the restriction identity for a
measurable equivalence and the published slice correspondence. Therefore
`integrable_lowerMeasure_iff` transfers genuine Bochner absolute integrability in both
directions, and `integral_lowerMeasure` transports each restricted Banach-valued integral.
Its complex specialization gives the integrand identity, and its real specialization
applied to the norm gives the norm identity. The latter equalities also hold for total
integrals without convergence, so they are not claimed to establish convergence.

`compatible_measure_data` uses the published right invariance of `unipotentHaar` and the
published compatible standard quotient construction for exactly `generalLinearHaar` and
`unipotentHaar`. Every compatible measure is regular by its compatibility property. The
quotient is locally compact, Hausdorff, and second countable, so this regular measure is
finite on compact sets and sigma-finite. A measurable equivalence preserves
sigma-finiteness, proving it for the prescribed lower transport.

These are derived measure facts, rather than the analytic growth argument of JPSS
Section 4.7. This module assumes no representation data and proves no outer integrability.
It leaves the existing target statement and its entire import closure unchanged.
The local canonical-field and general-linear instances have explicit names so
that this helper can be imported together with the independent growth modules.
