# The rank-zero ambient matrix-to-gamma comparison

Authors: Worker 64 (mathematical proof); Worker 458 (explicit local instance
names for compatibility with the positive-rank imports).

`Langlands.RankinSelberg.rankOneAmbientMatrixFunctionalEquationComparison_zero`
proves the `n = 0` branch of the existing ambient comparison. It covers every
prime and canonical p-adic field, supplied unitary additive character and
additive Haar measure, full rank-one Whittaker-type representation `σ`, and
specified nonzero Whittaker functional. The actual independent ambient
representation `ρ` has its own carrier universe. The field, original carrier
and ambient carrier universes `uF`, `uV`, `uW` are independent.

The hypotheses are precisely actual coefficient inclusion and unchanged
normalized matrix functional-equation data on `ρ`, with fixed `P`, `PDual`,
complex unit `c` and integer `a`. The conclusion is the full existing
`IsPadicSymmetricGammaFactor` for the original `σ` against the trivial
rank-one representation and the same rational gamma expression. The helper
works without a self-duality premise, so it applies to every self-dual measure
in the parent proposition. This is a conditional comparison, with no assertion
that the ambient matrix data exist.

## Independent nonzero model integral

The proof first shows full inverse Whittaker type for the trivial rank-one
representation by the published scalar-type theorem. Its chosen inverse
functional is `rankOneTrivialInverseFunctional`, the identity on `ℂ`, whose
nonzeroness is already proved.

The crucial witness is obtained independently of all ambient matrix data.
Apply the published `equalRankUnitValue.{uF,uV,0}` with the actual original
representation, the trivial rank-one representation, their specified nonzero
functionals, the canonical topological data, and `rankOneQuotientHaar`.
The published `rankOneQuotientHaar_isCompatible` supplies compatibility with
exactly the normalized group and unipotent Haar measures. The compact-test
construction gives literal membership of rational one in the original
`equalRankRationalValues` set. Since one is nonzero, it supplies the required
nonzero model continuation. No normalized-generator witness from `ρ` is used
for this step. The compact-test theorem uses actual model lifts and positive
finite compact quotient mass; it is independent of the general gamma-factor
and analytic-base results.

## Restricting the ambient equation

For each pair of actual model vectors and every row Schwartz--Bruhat test,
the proof pulls the test back through `oneByOneRow`. The ambient matrix data
supply a full-matrix Fourier witness, which is pulled back through the inverse
homeomorphism. `rectangularFourierIntegral_oneByOneRow` proves the actual
row Fourier identity. This uses the plus pairing and product of the same
supplied additive Haar measure, without a new normalization or scalar.

The definition `rankOneAmbientModelMatrixCoefficient` applies the published
`rankOneModelMatrixCoefficient`, which absorbs the constant second model vector into
the first and constructs an actual bi-smooth coefficient of the original
coefficient-model representation. The new definition uses the assumed inclusion to package that same
complex-valued function as an actual coefficient of `ρ`. Ambient original
and inverse-transpose matrix assertions then give their two continuations,
and the ambient matrix equation applies to exactly this coefficient and its
Fourier-related tests. The rank-one model-integral identities transport both
continuations by equality of the actual functions of the spectral parameter.
The matrix shift vanishes. The unsigned long Weyl matrix is the identity in
rank one, so the actual inverse-character dual is the inverse-transpose
coefficient without a signed-Weyl correction.

`NormalizedFunctionalEquation.gamma_value_of_regular` gives the equation on
the entire reduced-denominator domain, using the canonical residue
cardinality, `LocalFactor.coe_residueReflection`, and nonzeroness of the
ambient dual generator polynomial. Thus the ambient generators remain
assertions on `ρ`; the proof never asserts that either generates the smaller
model family.

Finally, `unipotentQuotientHaar_zero` identifies the constructed rank-one
quotient measure with the published normalized quotient Haar measure. The
published `equalRankGammaFactor_of_equation` transports the fixed-functional
equation to every compatible quotient measure and every nonzero functional
pair and supplies all existence clauses. Unfolding the equal-rank symmetric
convention gives the stated certificate for the original representation.

## Original sources and internal provenance

This module is an internal ambient extension of the published rank-one Tate
passage, rather than a transcription of a numbered source theorem. All
existing statement and imported Lean/Markdown pairs are unchanged.

Registered source `jps-1979-gl3-i`: H. Jacquet, I. I. Piatetski-Shapiro and
J. Shalika, *Automorphic forms on GL(3) I* (1979). Retained original:
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Automorphic Forms on GL(3) I--1979.pdf`.
SHA256: `6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
Printed p.177 fixes the matrix Fourier convention; p.181 describes the
rank-one character model. Proposition 3.1, pp.185--187, gives compact
averaging, with the function-space extensions on pp.183 and 188--190.
Section 4.4 and Theorem 4.5 with its proof, pp.194--198, explain the
higher-rank comparison, whose block range is empty at rank one. These
passages were read in the retained text layer, with the formula on p.177
also inspected in the scan. This helper supplies the separate rank-one
boundary, not a positive-rank block argument.

Registered source `jpss-1983-rankin-selberg`: the same authors,
*Rankin--Selberg Convolutions* (1983). Retained original:
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
SHA256: `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Sections 2.1--2.2, pp.385--386, give the full Whittaker-type and actual
coefficient scope; p.393 gives the compact unit-value test. Section 5.4,
pp.422--423, motivates ambient coefficient application. These five pages
were read visually in the retained scan. The present proof uses no
multiplicativity, Section 7 descent, generic-socle occurrence or gamma
invariance assertion from that later argument.

Both source fingerprints were checked. The registered index, project notes
and current Library notes contain no source-specific erratum affecting these
passages. The proof's precise provenance is composition of the existing
actual compact-test, coefficient, Fourier, quotient-measure and functional
uniformity theorems, together with the supplied actual inclusion. It adds
no irreducibility, occurrence, representation-equivalence, factor-existence,
nonvanishing or analytic-data premise.
