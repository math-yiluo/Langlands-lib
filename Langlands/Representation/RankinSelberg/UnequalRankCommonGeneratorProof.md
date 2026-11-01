# A common normalized generator for unequal-rank JPSS blocks

Author: Worker 12.

`Langlands.RankinSelberg.unequalRankCommonGenerator.{uF,uV,uW}` proves exactly
`UnequalRankCommonGeneratorStatement.{uF,uV,uW} F T n r` from
[AnalyticStatement](AnalyticStatement.md). Its binders are implicit
`{p : ℕ}`, `[Fact p.Prime]`, and explicit `F : PadicField.{uF} p`,
`T : F.TopologicalData`, and `n r : ℕ`.

For `n < r`, every pair of the target's Whittaker-type representations and
nonzero specified functionals has one polynomial `P : Polynomial ℂ` with
constant coefficient one whose reciprocal generates the Laurent span of
`unequalRankValuesAt j k` for every `r = n + (j + k + 1)`. The existential
choice of `P` precedes the arbitrary block indices `j,k`.

The full target telescope is retained: the supplied topology and normalized
absolute value, every compatible quotient measure `μ`, every supplied scalar
additive Haar measure `ν` and its actual rectangular product measures, and
independent field and representation universes `uF,uV,uW`. The representation
scope is the published `IsOfWhittakerType`, with no irreducibility restriction.
The theorem has no additional analytic, support or Fourier premise.

## Implemented proof

The proof imports the published
[unequalRankAnalytic](UnequalRankAnalyticProof.md) and
[unequalRankAdjacentBlockSpan](UnequalRankBlockSpanProof.md) theorems by their
Lean module names. The fourth clause of `unequalRankAnalytic` gives a
normalized generator at block zero, with `k₀ = r - n - 1`. The inequality
`n < r` proves the required equality `r = n + (0 + k₀ + 1)`. The local
`hgeneral` argument transports the fixed-rank representation and its specified
functional to that block by eliminating the rank equality. Its Whittaker-type
and nonvanishing hypotheses are preserved.

The private lemma `commonGenerator_of_adjacentSpan` is the finite algebraic
assembly. It chooses `P` from the block-zero generator before introducing
`j,k`, then inducts on `j`, generalizing `k`. At `j = 0`, rank arithmetic
forces `k = k₀`, so the initial generator applies. At the successor step,
the published equality of spans for `(j+1,k)` and `(j,k+1)` transports the
inductive generator equality. The proof keeps `P.coeff 0 = 1` unchanged and
composes only the span equality in `IsNormalizedGenerator`.

The adjacent-span theorem uses exactly the same `μ` and `ν` as the base
analytic theorem, including when the matrix has no rows. Its proof supplies
the compact-support, averaging and Fourier arguments for arbitrary supplied
Haar measures. This module only applies that result; it imposes no self-dual
normalization or replacement of the measures. All natural `n,r` are covered,
with the `n < r` implication already part of the target; rank gap one uses
only the base case.

## Original sources and provenance

The source is Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg
Convolutions* (1983), registered as `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Theorem 2.7(ii), printed pp.390–391, asserts a normalized reciprocal-polynomial
generator independent of the block index. The unequal-rank proof on
pp.393–394 establishes per-block principality and normalization, and
pp.394–395 compare adjacent ideals using Schwartz cutoffs and Fourier
smearing. Those pages were read for this work. The source's ranks are
`r_source = r + 1` and `t_source = n + 1`; our adjacent blocks are its
`a` and `a-1`.

The referred argument in Jacquet, Piatetski-Shapiro and Shalika,
*Automorphic Forms on GL(3) I* (1979), registered as `jps-1979-gl3-i`,
SHA256 `6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`,
Proposition 4.1.4 and Lemma 4.1.5, printed pp.188–190, supplies the
compact-support, smoothness, averaging and Fourier inclusions behind that
comparison. Those original pages were also read. The imported adjacent-span
proof's Markdown explains its implementation with the supplied measures.

The private induction and dependent-rank transport are internal assembly
steps, derived directly from the published `IsNormalizedGenerator` definition
and adjacent-span equality. They assert no additional result from the
original literature. Worker 329 authored the imported analytic proof, and
Worker 180 authored the imported adjacent-span proof; those proofs and their
prerequisites are reused by import. Only this new proof pair is submitted.
