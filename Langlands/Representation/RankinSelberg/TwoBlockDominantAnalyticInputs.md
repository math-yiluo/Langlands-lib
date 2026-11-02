# Uniform analytic inputs for the dominant first-block identity

Author: Worker 1209.

This internal assembly proves the analytic clauses needed by the dominant
first-block calculation in JPSS, *Rankin–Selberg convolutions* (1983),
Section 4.10(2), printed page 419. The registered original is
`jpss-1983-rankin-selberg`, retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The single-threshold formulation, separate determinant-slice absolute-input
conditions and inclusion of zero supplied functionals are internal deductions.
They are not a literal theorem statement of the source. The proof combines
ordinary Jacquet realization, upper slice analysis and actual lower raw-norm
convergence. It does not prove the finite Laurent identity.

`compatible_standard_quotients F t a` gives right-invariance certificates and
compatible quotient measures at both specified ranks, with the exact existing
`generalLinearHaar` and `unipotentHaar` normalizations. It uses the published
right-invariance and standard unipotent quotient existence theorems. These
choices precede and are independent of representations, additive Haar measure,
sections and tests. Later clauses retain every compatible supplied measure,
independently of these existential witnesses.

`HasUniformAnalyticInputs` is a Prop-valued predicate. A real bound `C` precedes
the opposing real twist `u`, all supplied right-invariance certificates and
compatible quotient measures, both complementary dimensions, every induced
section and ambient coefficient-image test, and every determinant index. For
each `u > C`, it asserts absolute convergence of the ordinary Jacquet integral
for every section and chooses one actual inverse-character functional `J` on
the entire induced representation. The coefficient identity realizes the
ordinary integral at every group element. The functional is nonzero whenever
both originally supplied block functionals are nonzero; neither convergence
nor realization requires this premise.

For every compatible supplied pair `nuN, nuA`, the predicate asserts
sigma-finiteness of both measures and of exactly
`nuMinus = Measure.map (lowerToStandard h F.Carrier).symm nuN`. For every
`j,k,hr,f,Wtest`, it uses the actual ordinary-Jacquet coefficient of `J,f` and
the exact rank transport `hr` of the ambient coefficient. The upper rectangle
measure is the supplied finite product Haar measure; its Borel version is
`rectangularBorelMeasure`, the equality transport defined in
`TwoBlockDominantUpperSliceAnalysis`. Unfolding that definition gives exactly
the transport by `BorelSpace.measurable_eq` in the closed target. No mass,
measure scale or map is introduced by that equality transport.

The upper rectangle average and actual lower quotient kernel at spectral
parameter zero are measurable. On every actual determinant slice the
predicate separately asserts:

1. Integrability of the upper integrand on the product of the restricted
   supplied quotient measure and the original upper rectangle measure.
2. Integrability of the actual complex lower rectangle average under the
   restricted prescribed lower measure.
3. Integrability of the actual real integral of the pointwise lower kernel
   norm under that same restricted lower measure.
4. Almost-everywhere integrability of the actual lower rectangle fiber under
   that same restricted measure.

The lower functions retain both original rectangles and their supplied product
Haar measure. The third condition concerns the real raw-norm profile, not the
norm of the complex average. No convergence conclusion is inferred from a
value of a totalized integral.

`exists_uniform_analytic_inputs` takes the maximum of the bounds supplied by
`exists_uniformOrdinaryJacquetRealization` and
`exists_uniform_slice_convergence`. The ordinary result supplies convergence
and one functional before every supplied quotient measure and test.
`standardCompatible_sigmaFinite` supplies finiteness at the large standard and
lower quotients; `compatibleQuotient_sigmaFinite` supplies it at the first-block
quotient. Both arguments retain the exact measures supplied by the caller.

For each complementary pair, rewriting along `hr` puts the ambient
representation at the required upper rank. The actual twisted blocks retain
full Whittaker type, so `lowerInduced_inverseWhittakerType` gives full inverse
Whittaker type of the actual induced representation.
`continuous_upperAverage` gives measurability, and `upperSliceConverges` gives
genuine upper product convergence for this same `J,f`. The uniform lower
result supplies measurable kernel and actual absolute input on each slice.
`lowerMeasure_restrict` converts its standard restricted-measure presentation
into the explicitly prescribed restricted lower measure. This is an exact
measure equality and does not rescale or replace the supplied measure.

The field, ambient carrier and dependent block carriers retain independent
universes `uF,uV,uW`. Full Whittaker type permits reducible representations.
All supplied functionals, including zero, all positive block sizes and all
natural complementary dimensions satisfying `hr`, including zero dimensions,
remain allowed. No small-block epsilon certificate or factor existence premise
is used. The result does not assert global outer convergence at spectral
parameter zero and leaves the first-block functional equation and finite
Laurent convolution identity to separate work.
