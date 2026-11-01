# Positive-rank comparison using ambient matrix data

Author: Worker 458.

This internal extension proves `AmbientMatrixComparison.gammaFactor` for every
positive rank `m + 2`. It retains independent field, original-carrier and
ambient-carrier universes, full Whittaker type for the original representation,
a specified nonzero Whittaker functional, the supplied additive character and
self-dual additive Haar measure, actual bi-smooth coefficient inclusion, and the
unchanged normalized matrix functional-equation data on the ambient representation.
Its conclusion is the complete existing symmetric gamma-factor certificate for
the original representation against the trivial rank-one character, with the
specified polynomials, complex unit and integer exponent. It is conditional on
the data and asserts no existence of that data.

## Actual coefficient inclusion and convergence

`AmbientMatrixComparison.coefficient` views an actual coefficient of the
coefficient-model representation as an ambient coefficient. The function is
identical; its membership proof is the supplied submodule inclusion. There is
no map from the original carrier to the ambient carrier and no assertion of a
representation equivalence or occurrence.

The ordinary and inverse-transpose common convergence bounds restrict through
this definition. The normalized-generator assertions stay on the ambient
representation. In particular, the proof never attempts to obtain the entire
matrix analytic assertions on the smaller family with the ambient polynomials.

`firstDualMatrixConvergesOnRight` uses the published inverse-transpose
convergence transport and the actual `firstDualModelRepresentationEquiv` to
obtain ordinary convergence on the first-dual model. The equality of the
bi-smooth coefficient submodules transports the same bound. The helper
`dualBlockZeroConvergesOnRight` applies the existing finite-expansion block
convergence theorem to that first-dual model, including its translated vectors.
The second dual of the trivial canonical vector is the trivial vector for the
inverse additive character. This identifies the literal complementary block.
`rankOneDualBlockConvergesOnRight` then uses the existing quotient/product
integrability identity to get genuine convergence of the signed-dual block
integrand used in principal-box extraction. These steps require convergence,
not a normalized generator on the model.

## One principal realization and one common scalar

`principalDualAssertions` adapts the published principal-dual proof by supplying
only the preceding convergence bound. It intersects the original, raw
inverse-transpose, and dual-block half-planes. Fourier invariance of the
principal-box test and the proved paired compact-averaging identity identify
the averaged coefficient integral with the original function integral.
`principalDual_value` then gives the actual complementary dual value. Its
published signed-Weyl conversion is retained unchanged, including the supplied
character's conductor and supplied measure's Fourier normalization.

`pairedMatrixBlockComparison` chooses a single principal realization for each
original model vector. The box-extraction constant is positive, hence its
complex image is nonzero. The original extraction and the just-proved dual
extraction use the same box test, actual averaged bi-smooth coefficient, and
constant. The dual assertion holds for every Fourier partner of that test.
The resulting `PairedMatrixBlockComparison` compares the literal original
block-zero and complementary-dual block integrals on right half-planes.

## Continuations and the full equation

`gammaFactor` first restricts the two common convergence bounds from the
ambient data. The published raw convergence lemma applies to the actual model
function; shifting its threshold by the real part of `jpssShift` gives the raw
bound used in the paired comparison.

For each vector, let `C` be the comparison's common nonzero scalar. Embed its
averaged coefficient using `coefficient`. The ambient data give a Fourier
partner and actual shifted rational values `RM` and `RMd` for this same
coefficient. Define the block values by

- `R = RatFunc.C (C⁻¹) * RM`;
- `Rd = RatFunc.C (C⁻¹) * RMd`.

Constant multiplication preserves rational continuation. Each paired
half-plane equality identifies the corresponding inverse-scaled matrix integral
with the literal block integral, so `continuation_of_eq_on_right` supplies
both required block continuations directly. No model normalized generator or
independently assumed model continuation is used.

The ambient normalized equation is an equation for `RM` and `RMd`. Algebraic
identities rewrite these as `RatFunc.C C * R` and `RatFunc.C C * Rd`.
The published `NormalizedFunctionalEquation.of_const_mul` cancels `C` while
preserving the entire reduced-denominator domain of the unscaled values.
The ambient dual normalized generator supplies only the necessary nonzeroness
of `PDual`. The existing
`rankOneGammaFactor_of_normalized_blockZero_one` converts this block-zero
normalized equation into the complete symmetric gamma certificate. That
published adapter supplies independent nonzero model integrals from compact
tests, absorbs arbitrary trivial second vectors, propagates to every allowed
complementary block, and transports to every compatible quotient measure and
nonzero functional pair. Thus the result concerns the original representation,
including reducible full-Whittaker-type representations.

## Sources and provenance

This is derived internal infrastructure for the ambient extension, not a
literal numbered theorem in the sources. It adapts only the convergence
interfaces and continuation assembly of the existing matrix-to-rank-one proof.
Every statement pair and imported Lean/Markdown pair remains unchanged.

Registered `jps-1979-gl3-i`, Jacquet--Piatetski-Shapiro--Shalika,
*Automorphic forms on GL(3) I* (1979), SHA256
`6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`:
printed p.177 fixes the matrix/Fourier convention; Proposition 3.1 on
pp.185--187 supplies compact averaging; the function-space discussion on
p.183 and pp.188--190 explains why this comparison must concern the actual
function family; Section 4.4 and Theorem 4.5 with its proof on pp.194--198
supply the matrix/rank-one comparison context. These passages and the displayed
formulas were read in the registered original.

Registered `jpss-1983-rankin-selberg`, the same authors,
*Rankin--Selberg Convolutions* (1983), SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`:
Section 5.4, pp.422--423, read in the scanned original, motivates applying a
matrix equation from an ambient family. The present proof does not use that
section's multiplicativity argument, Section 7 descent, analytic-base factor
existence, generic-socle occurrence, or gamma invariance. The registered index
and current project/Library notes contain no source-specific erratum affecting
the cited passages.
