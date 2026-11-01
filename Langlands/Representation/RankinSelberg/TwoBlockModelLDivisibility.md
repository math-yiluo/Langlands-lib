# Rank-one L divisibility through actual coefficient quotients

Worker 468 authored this internal derived proof. The analytic context is JPSS,
*Rankin–Selberg Convolutions* (1983), Theorem 3.1, printed pp. 404–405,
Section 5.3, printed p. 422, and Section 7.1(3), printed pp. 438–439.
The registered source is `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The proof below is a composition of published Library results. Its matrix
induction argument acts directly on the actual upper normalized induction,
using the forward expansion and reverse realization of full matrix tests. It
does not transfer a lower induced representation by merely commuting factors.

`twoBlockLRankOne_of_uniform_mellin.{uF,uV,uW}` proves the existing full
`TwoBlockLRankOneStatement.{uF,uV,uW}` from exactly the explicit premise
`UniformFiniteFunctionMellinConvergenceStatement.{uF}`. The exact closed
wrapper in `TwoBlockRankOneProof` supplies the published theorem
`uniformFiniteFunctionMellinConvergence` to this premise.

The two local canonical instances in `ModelInclusion` have explicit names,
`twoBlockModelLTopology` and `twoBlockModelLGLMeasurable`, so this helper
composes with the shared matrix functional-equation imports. Their types,
values, order and locality are unchanged.

## Coefficients of a genuine quotient

`GodementJacquet.biSmoothMatrixCoefficients_le_of_surjective` takes a smooth
representation `rho`, any quotient representation `tau`, and a surjective
intertwiner `q : rho -> tau`. For each actual bi-smooth coefficient of `tau`,
lift its smooth vector to a vector of `rho`. Smoothness of `rho` makes this
lift smooth. Pull its smooth functional back using the algebraic dual
intertwiner; `isSmoothVector_map` proves that this pullback remains smooth.
Intertwining identifies the entire coefficient functions. Span closure gives
`biSmoothMatrixCoefficients tau <= biSmoothMatrixCoefficients rho`.
No topological group or compact-cofinality hypothesis is needed here.

`matrixRationalValues_subset_of_coefficients_le` retains the same full matrix
test, the same scalar coefficient function and the same rational continuation
under such a coefficient inclusion. The actual measure, normalized absolute
value and JPSS shift are unchanged.

`model_jpssI2_le_of_surjective` specializes this to a full Whittaker-type
source `rho`, a smooth quotient `tau`, and specified nonzero functionals on
both. The published
`coefficientModel_eq_of_surjective_of_whittakerType` identifies only their
actual coefficient images, as invariant subrepresentations of the common
Whittaker function space. The induced linear equivalence transports the model
coefficient spaces. The canonical surjection from `tau` onto its own model
then gives inclusion of the source model's matrix coefficient space in that
of `tau`. Passing to the same rational values and their Laurent spans proves
`jpssI2(model rho) <= jpssI2(tau)`. Neither original representation is asserted
to be equivalent to its model; their coefficient maps can have kernels.

## Symmetric certificates

`isPadicSymmetricLPolynomial_rankOne_one_swap` exchanges the trivial rank-one
scalar representation with the other member of a full symmetric L
certificate. In actual rank one, the published fixed-character equal-rank
swap theorem is required. In larger rank, both symmetric definitions select
the same larger-rank-first ordered certificate. This preserves the entire
certificate, including its compatible-measure existence witness and universal
measure and functional quantifiers.

## Two-block divisibility

First apply the published `twoBlockLRankOne_of_trivial_test`. Its premise
retains arbitrary full Whittaker-type blocks. Choose a nonzero Whittaker
functional on each original block `sigma i` and let `tau i` be its actual
coefficient model. Full type of each `tau i` is supplied by
`glCoefficientModel_isOfWhittakerType`. The polynomial `Pi i` is the published
`modelMatrixLPolynomial` of the original block; it has the complete supplied-
measure symmetric pair certificate. `modelMatrixAnalyticAssertions` supplies
the three ordinary matrix analytic assertions for `tau i` at this polynomial,
using the sole explicit premise `hU` for common convergence.

Let `I` be upper normalized induction of the original ordered block family,
and `J` upper normalized induction of the model family. The published
`normalizedProductModelMap` is an actual surjective intertwiner `I -> J`;
its surjectivity uses smoothness of the original blocks. The published
`normalizedProductWhittakerType` supplies full type of both `I` and `J` and
hence nonzero functionals on each. No full type or functional existence is
added as a premise.

For `J`, apply `twoBlock_matrixGeneratorInputs` and
`matrixAnalyticAssertions_twoBlock_of_generators` to the two ordinary block
analytic assertions. These published results supply common convergence,
forward product-module rationality and reverse realization of block values,
and assemble the actual matrix generator `prod i, Pi i` for `J`. They require
smooth admissible blocks; no central character, transformed assertion or
functional equation is assumed. All constructions use the actual upper
parabolic and the entire ordered block family.

Choose `P = modelMatrixLPolynomial` for `I`. It has the complete symmetric
pair certificate for `I` against the trivial scalar test, and its reciprocal
generates `jpssI2(model I)` by `modelMatrixLPolynomial_normalized`. Applying the
model quotient inclusion above to `I -> J` gives
`jpssI2(model I) <= jpssI2(J)`. The published
`normalizedGeneratorSpanDivisibility` gives exactly `P` divides `prod i, Pi i`.
For a witness `prod i, Pi i = P * Q`, commute the two factors on the right and
choose `e = 0`, obtaining precisely
`X ^ e * prod i, Pi i = Q * P`. The swap lemma puts both full symmetric
certificates in the test-first order required by the published target.

Finally the trivial-test reduction handles an arbitrary full Whittaker-type
rank-one test on its independent carrier. It constructs an actual equivalence
to a continuous scalar quasicharacter, twists the entire ordered block family,
uses the actual normalized-product determinant-twist equivalence, and transports
the full certificates back. The polynomials and witnesses remain unchanged.

## Discharged and explicit inputs

All model rationality, ideal comparison, symmetric L existence, full induced
Whittaker type, genuine quotient surjectivity, matrix expansion and reverse
realization interfaces above are discharged by their named published proofs.
Only uniform Mellin convergence is explicit in this helper; the closed wrapper
discharges it with `UniformFiniteFunctionMellinConvergenceProof`.

The canonical field, nontrivial character, supplied self-dual Haar measure,
dependent positive block ranks and independent universes are retained. Reducible
originals and rank-one blocks are included. No unrestricted two-block or
finite-block multiplicativity, Section 7 descent, later multiplicativity result,
functional equation or gamma-factor existence is used. This file supplies the
L argument; `TwoBlockRankOneProof` also closes the separate gamma target
through the generic matrix functional-equation theorem.
