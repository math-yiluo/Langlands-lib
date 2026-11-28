# Twisted orbital integrals on a finite product

`Langlands.TraceFormula.piTwistedOrbitalIntegral` proves
`PiTwistedOrbitalIntegralStatement` with arbitrary factor and index universes.
It establishes integrability of the product orbit function and the product
formula for its integral. The finite-product integrations include the empty
family, for which the integral is `1`.

The componentwise twist identifies the centralizer with the product of the
factor centralizers. The map `leftQuotientPiHomeomorph` from
`Langlands.Analysis.Local.LeftQuotientProduct` sends the class of a tuple to
the tuple of its classes. Closedness follows from `isClosed_twistedCentralizer`
in `Langlands.BaseChange.RegularTransferMeasures`. The factor centralizers and
quotients are locally compact and second countable. The quotient topology uses
`leftQuotient_t2Space`, `leftQuotient_locallyCompactSpace`, and
`leftQuotient_isOpenQuotientMap` from `Langlands.Group.LeftQuotient`. The
quotient measures are regular by compatibility. These facts give the
sigma-finiteness used by finite Fubini, with Mathlib's
`MeasurableEmbedding.sigmaFinite_map` for the subgroup pushforwards.

To identify the quotient measure in these coordinates, the proof tests against
products of compactly supported continuous real functions on the factor
quotients. It lifts each factor test to a compactly supported continuous
function on its group using `exists_positiveLifting_of_isMulRightInvariant`
from `Langlands.Analysis.Local.QuotientCompatibleScaling`. The fiber average
of the product of these lifts is the product of their factor averages. The
proof computes the averages on coset representatives using
`quotientAverageReal_mk` from `Langlands.Analysis.Local.QuotientAverageReal`,
uses `IsClosedEmbedding.integral_map` for the subgroup inclusions, and applies
`integral_fintype_prod_eq_prod` to the specified product of the centralizer
pushforwards. The quotient measure is transported using `integral_map_equiv`.
Applying `IsCompatible.integral_quotientAverageReal` from
`Langlands.Analysis.Local.QuotientAutomorphismProof` and finite Fubini on the
ambient group shows that the transported measure and the product of the
factor quotient measures give equal integrals for every such product test.

For a compact subset of an open rectangle, Mathlib's
`exists_continuous_one_zero_of_isCompact` supplies a cutoff in each coordinate
equal to `1` on the projection of the compact set and zero off the open side.
Their product is `1` on the compact set, lies in `[0,1]`, and is zero off the
rectangle. `Integrable.measure_le_integral` and `integral_le_measure` use
equality of the tensor integrals to bound the compact set's measure for
either measure by the rectangle's measure for the other. The transported
measure is regular by `Measure.Regular.map`. The product measure is regular by
`Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure`.
`IsOpen.measure_eq_iSup_isCompact` gives equality on open rectangles.
Mathlib's `Measure.pi_eq_generateFrom`, using the open sets and their finite
spanning sequences from `Measure.finiteSpanningSetsInOpen`, identifies the
two measures.

In coset coordinates the twisted orbit function is the product of the factor
orbit functions by `twistedOrbitFunction_mk` from
`Langlands.TraceFormula.TwistedOrbital`. Mathlib's `Integrable.fintype_prod_dep`
and `integral_fintype_prod_eq_prod` give the two conclusions. The proof
transports them along the measure-preserving equivalence of quotients using
`MeasurePreserving.integrable_comp_emb` and `MeasurePreserving.integral_comp`.

The finite splitting comes from Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), Lemma 17.8.3 and (17.55), printed pp. 463–464. The
twisted integrand and left-quotient integration come from (18.32), printed
p. 487. The retained source `getz-hahn-2024-automorphic-representations` has
SHA-256 `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
[Getz–Hahn (2024)](https://doi.org/10.1007/978-3-031-41153-3)
