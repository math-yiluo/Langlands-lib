# Real analyticity of the actual Cartan polynomial coefficients

`Langlands.Global.ArchimedeanGL.CartanPolynomialCoefficientAnalyticityStatement K n`
is a proposition definition concerning the published, explicitly constructed operator
`cartanPolynomialCoordinateOperator K n p`. For every number field `K` in any
universe, every natural rank `n`, and every complex polynomial `p`, each
coefficient is real analytic near every point of the original ambient space
`ArchimedeanMatrix K n`. The source norm and topology are the existing ones;
the scalar values are complex and analyticity is over the real numbers.

The proposition is stronger than coefficient analyticity only on the units
domain. It includes the zero polynomial, constant polynomials and rank zero,
and assumes no monicity. It uses the fixed real basis and bounded ordered-word
arrays of `Langlands.Global.ArchimedeanCartanPolynomialCoefficients` without
altering their definitions. The imported `AnalyticCoefficientsOn Set.univ`
quantifies over every allowed order, every ordered coordinate word of that
length and every ambient point.

The provenance is internal: this is one correctness obligation for the explicit
recursive construction, not a transcription of an external theorem. The intended
proof follows the recurrence. Continuous real linear moving fields and coordinate
functionals are analytic. Analytic coefficient functions have analytic real
Frechet derivatives; continuous bilinear evaluation, products, zero extension,
finite sums, induction on Cartan iterates and the finite polynomial sum preserve
analyticity. Acceptance of this proposition does not provide that proof.

This unit asserts only coefficient analyticity. It does not identify the action
with `cartanAmbientPolynomial`, compute its highest-order symbol, prove
ellipticity or establish analytic regularity of solutions. Those remain separate
obligations in the published coordinate realization and joint-finite analyticity
statements.

Worker 116 formulated the proposition from the published coefficient construction.
Worker 459 checked the full proposition telescope against the published carrier
and prepared this pair for independent review.
