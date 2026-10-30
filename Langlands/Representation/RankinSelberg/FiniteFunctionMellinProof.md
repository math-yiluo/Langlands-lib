# Finite-function torus Mellin analysis: proof

`Langlands.RankinSelberg.finiteFunctionMellin.{uF}` proves exactly
`Langlands.RankinSelberg.FiniteFunctionMellinStatement.{uF}` at arbitrary
field universe `uF`. It applies the assembly helper
`MellinAssembly.finiteFunctionMellin_of_inputs` to the published proofs
`Langlands.RankinSelberg.finiteFunctionTensor` and
`Langlands.RankinSelberg.oneVariableMellin`. The Schwartz–Bruhat tensor
expansion comes from the published theorem
`Langlands.HarmonicAnalysis.rowTensorDecomposition`.

The theorem retains every prime, supplied field and topological data,
dimension, positive integral weight vector, and finite family of continuous
translation-finite functions. For each family member and arbitrary
Schwartz–Bruhat test it proves actual Bochner integrability on a right
half-plane and rational continuation of the actual Mellin integral in
`q^(-s)`, where `q` is the supplied residue cardinality. One nonzero Laurent
denominator clears all continuations for all these tests and family members.
The supplied normalized absolute value and product of normalized
multiplicative Haar measures are retained, including dimension zero.

This is a derived assembly argument following the reductions on printed
page 392, displays (5)–(6), of Jacquet–Piatetski-Shapiro–Shalika,
*Rankin-Selberg Convolutions* (1983), registered source
`jpss-1983-rankin-selberg`. The original is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
The finite-function predicate is continuity and finite-dimensional complex
left-translation span, as in the target and the definition before Proposition
(2.2) on printed page 181 of *Automorphic Forms on GL(3) I* (1979),
registered source `jps-1979-gl3-i`. The general measure-space helpers and
empty-product case are internal derived content, not verbatim source theorems.

## Implemented argument

`localHaar_sigmaFinite` derives second countability for the supplied topology
from `T.secondCountableTopology` and transfers it to the unit group via
`Units.isEmbedding_val₀`. Unfolding the actual normalized multiplicative
Haar construction gives Mathlib's sigma-finiteness instance. It does not choose
a different Haar measure. `field_totallyDisconnected` transports the
nonarchimedean-ring certificate along
`Valuation.toTopologicalSpace_eq` and uses Hausdorffness from `T.fieldT2`.
These facts supply the product integration and Schwartz tensor hypotheses
for exactly the supplied field realization. The assembly applies the published
`rowTensorDecomposition` theorem with this topology and its local compactness,
Hausdorffness and total disconnectedness instances.

`continuation_mul` and `continuation_prod` intersect finitely many right
half-planes, use divisibility of reduced denominators, and preserve
reduced-denominator nonvanishing. `commonDenominator_iUnion` multiplies the
nonzero Laurent denominators of finitely many sets. The product-set version
multiplies both denominators and numerator witnesses.

`uniform_right` bounds a finite range of real convergence thresholds.
`sum_prod_analytic` then proves integrability of finite linear combinations
of coordinate products by `Integrable.fintype_prod_dep`. On a common right
half-plane it distributes the actual Bochner integral over the sum and applies
`integral_fintype_prod_eq_prod`. The resulting integral has the finite linear
combination of products of the scalar rational continuations as a continuation.
The empty coordinate and summation index types are included.

`tensor_expansion_identity` distributes both finite tensor expansions and
collects each coordinate's test, finite function and spectral factor.
`mellin_of_expansions` fixes the finite-function expansion first. For each
coordinate factor it considers the set of all one-variable continuations as
the scalar test varies. Products of these sets, and their finite union over
the fixed finite-function expansion, have a common denominator. Each varying
test's assembled continuation belongs to the Laurent span of that same union.
Published continuation uniqueness, using `1 < q`, transfers this span
membership to every continuation of the integral. Thus the denominator remains
independent of the test, including when a different continuation is supplied.

`mellin_family_of_each` combines the denominators for a finite family using
its finite subtype. `finiteFunctionMellin_of_inputs` applies these helpers to
the supplied normalized absolute value and the positive integral weights,
with `T.residueCardinality_gt_one` for uniqueness. The final theorem
`finiteFunctionMellin` discharges both helper premises with the published
proofs at the same field universe. Thus the exact target has no additional
premises. Finite-product integration and the tensor decompositions cover
empty tuples; finite unions and spans also cover the empty family and zero
functions.

## Dependencies and attribution

Finite-sum continuation, Laurent-span membership and closure under a specified
denominator are imported from the published
`RationalContinuationLinearProof`, authored by Workers 64 and 329.
The product-continuation proof pattern adapts that published sum proof.
No unpublished peer proof was incorporated.
Mathlib supplies finite-product integrability and integration. The local-field
topology facts come from the published `PadicScalarHaarScalingProof` and its
imports.

The finite-function tensor proof is imported from
`Langlands.Representation.RankinSelberg.FiniteFunctionTensorProof`,
authored by Worker 650. The scalar analytic proof is imported from
`Langlands.Representation.RankinSelberg.OneVariableMellinProof`,
assembled by Worker 656 with the credited spectral adaptations from
Worker 235. These are published dependencies, reused by declaration name.

The scalar statement receives continuity and finite-dimensionality as separate
arguments. The finite-function tensor statement needs only a monoid and an
arbitrary topology; no continuity-of-multiplication assumption is added here.
The Schwartz result is imported from
`Langlands.HarmonicAnalysis.RowTensorDecompositionProof`, authored by Worker 128.
Its proof is reused as a published dependency, without copying its source.

Worker 352 wrote the multivariable assembly. The imported scalar theorem
provides its convergence, rationality and uniform-denominator conclusions;
the assembly proves their preservation under the fixed finite-function
expansion, arbitrary test expansion, and finite-family closure.
