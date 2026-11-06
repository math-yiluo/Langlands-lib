# Actual parabolic probabilities with proved Weil compatibility

The intrinsic actual radical quotient measures from
`GroupSchemeParabolicMeasure` are now bundled with their probability
and exact counting-measure Weil compatibility laws, without a supplied
right-invariance premise on radical Haar.

The module first treats any actual adelic subgroup functor whose
evaluated adelic subgroup is closed and whose actual rational quotient
is compact. Its principal subgroup is discrete by the existing
actual-point theorem. The existing quotient Haar measure is locally
finite, and compactness makes it finite. The public theorem
`LeftCosetSpace.isMulRightInvariant_haar_of_isFiniteMeasure` from
`LeftCosetSemidirectFiniteVolume` therefore proves right invariance of
the actual ambient subgroup Haar measure. Its exact hypotheses need
only the available locally compact, second-countable Borel topological
group and the finite actual quotient measure. No normality or algebraic
modulus computation is used.

That derived right invariance supplies the earlier analytic gate in
the normalized measure construction. The resulting bundle contains
the unchanged intrinsic mass-one quotient measure, its probability
law and its exact compatibility with the simultaneously normalized
ambient Haar and subgroup counting measure. Positive quotient
translation is measure preserving for that same measure.

For every proper rational parabolic of the connected reductive group,
the actual closed radical image and compact rational quotient are
already proved. The new complete family therefore uses exactly
`properParabolicQuotientMeasure` and `properParabolicHaarMeasure`,
with no renormalization or measure transport. It also proves subgroup
left invariance of the original normalized constant term without the
previous supplied subgroup right-Haar premise.

The mass-one convention agrees with Mœglin–Waldspurger,
*Spectral Decomposition and Eisenstein Series* (1995), I.1.13,
printed page 18, first paragraph. That passage supplies the normalization
convention; the finite-covolume argument here is an internal application
of the existing public theorem.

This is an internal actual-measure construction and reuse bridge.
The proper-parabolic dynamic theorem and connected reductivity remain
explicit. The result does not prove general reductive or norm-one
adelic unimodularity, finite volume of those quotients, conjugation
modulus comparisons, constant-term archimedean regularity or spectral
claims.
