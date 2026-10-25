# Sharp square-integrable convergence and holomorphy at zero rows

Worker 331, with PDF pagination correction by Worker 192.

This module defines the closed proposition
`Langlands.RankinSelberg.SquareIntegrableZeroRowAnalyticStatement.{uF,uV,uW}`.
It states absolute convergence and holomorphy of the actual unequal-rank
Rankin–Selberg integral at rectangular block `j = 0` throughout
`{s : ℂ | 0 < s.re}`. It is a statement target, not a proof.

## Quantifiers and hypotheses

Every prime `p`, field `F : PadicField.{uF} p`, compatible supplied
`T : F.TopologicalData`, and pair `n k : ℕ` is quantified. The local
instances use `T.topology`, `T.valuativeRel`, `T.localField`, and the Borel
measurable structures on the field, smaller general linear group, its
upper unipotent subgroup, and its left-unipotent quotient. The absolute
value is exactly `normalizedAbsoluteValue T`. This is the p-adic
specialization of the source's non-Archimedean local-field result;
`T` need not be the canonical choice.

`UnitaryAdditiveCharacter` already includes continuity, nontriviality and
unit-circle values. The first model uses `glFunctionals ψ`, and the second
uses `glInverseFunctionals ψ`. The statement retains the explicit
`Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)` instance. It
quantifies every quotient measure `μ` satisfying `IsCompatible` with the
published `generalLinearHaar` and `unipotentHaar`, and every additive Haar
measure `ν`. No self-dual choice is imposed.

The complex representation carriers `V : Type uV` and `W : Type uW` have
independent universe parameters. The larger rank is literally
`n + (0 + k + 1) + 1`, and the smaller is `n + 1`. This retains the rank
expression expected by `unequalRankModelIntegral` and its functionals,
so the statement needs no replacement representation or rank cast.
All positive rank gaps `k + 1` occur, including corank one at `k = 0`
and a rank-one smaller group at `n = 0`.

Both representations are assumed irreducible and analytically
square-integrable through `T.IsSquareIntegrable` from
`Classification.Tempered`. That predicate uses every Borel Haar measure
on the actual quotient by the center and `IsSquareIntegrableModCenter`:
admissibility, a unitary central character with its scalar action, and
`MemLp` with exponent two for the norms of all smooth matrix coefficients.
It is not a segment-classification or tempered-support replacement.
The statement adds no genericity, convergence, holomorphy, or factor-existence
hypotheses.

Every functional and every vector in its actual `coefficientModel` is
quantified. Nonzero-functional hypotheses are unnecessary: the coefficient
model of a zero functional contains only the zero function, so either
zero functional makes the integrand identically zero. For nonzero
functionals these are the Whittaker models occurring in the source.
This zero-functional extension is elementary derived scope.

## Integral and conclusions

Write the source ranks as `r = n + (0 + k + 1) + 1` and `t = n + 1`.
Then `r - t = k + 1`. The source integral is

\[
\Psi(s,W,W';0)=
\int_{N_t\backslash G_t}
 W(\operatorname{diag}(g,I_{r-t}))\,W'(g)\,
 |\det g|^{\,s-(r-t)/2}\,dg.
\]

The Lean statement uses the existing product measure
`rectangularMeasure ν 0 (n + 1)` exactly as supplied.
`rectangularMeasure_zero_rows` identifies it with unit point mass at
the unique zero-row matrix, and `unequalRankMatrix_zero_rows` identifies
the block matrix with the diagonal inclusion. These facts explain the
source correspondence without changing the measure or integral in the
statement.

For each pair of coefficient-model vectors the conclusion is a conjunction:

1. For every `s` with `0 < s.re`, `UnequalRankConverges` holds. This is
   Bochner integrability of the joint integrand under
   `μ.prod (rectangularMeasure ν 0 (n + 1))`, hence absolute convergence.
2. `DifferentiableOn ℂ` holds on the same open half-plane for the actual
   `unequalRankModelIntegral`, which integrates the rectangular variable
   first and then the quotient variable. The function is not a chosen
   rational continuation or an abstract factor.

Only zero rows are asserted. The common-generator theorem is a separate
ingredient for transferring the normalized denominator to other blocks.
Neither rationality nor existence of a normalized generator is asserted
or assumed here, and no claim is made at the boundary `Re(s) = 0`.

## Original source and restriction estimate

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, Section 8.3, printed pp.448–451.
The registered source is `jpss-1983-rankin-selberg`, with SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
These four pages were read visually from PDF pages 83–86 (one-based),
that is, indices 82–85 (zero-based).
No registered errata note for this source was found in the project
literature index or the public/project `notes/errata` locations.

The proposition on p.448 states absolute convergence in `Re(s) > 0`,
uniformly when the real part lies in a compact subset of that range.
Its unequal-rank assertion is specifically `Ψ(s,W,W';0)` for `r > t`.

On p.449, the quotient integration formula (1), square-integrability
modulo `N_r Z_r`, and compact-group finiteness give the restriction
integral (2) on `N_(r-1)\G_(r-1)`. On p.450, formula (6) yields the
crucial stronger restriction estimate (7):

\[
\int_{N_t\backslash G_t}
  |W(\operatorname{diag}(g,I_{r-t}))|^2
  |\det g|^{-(r-t)}\,dg < \infty.
\]

The same page writes the zero-row integral displayed above and explains
that the last row of `g` lies in a fixed compact set wherever the
restricted `W` is nonzero. One can therefore insert a nonnegative
Schwartz–Bruhat cutoff in that row. On p.451, Cauchy–Schwarz bounds the
square of the resulting absolute integral by the product of (7) and
the smaller-rank integral

\[
\int_{N_t\backslash G_t}
 |W'(g)|^2 \Phi(\eta_t g)^2 |\det g|^{2\operatorname{Re}(s)}\,dg.
\]

The latter is finite by the preceding equal-rank argument for positive
real part. The conclusion is convergence on the open half-plane.
The bridge from the Library's matrix-coefficient definition of
square-integrability to the source's Whittaker restriction estimates is
part of the future proof obligation, not an extra hypothesis here.

## Provenance of holomorphy

The source proposition claims local uniform convergence. At the end of
the proof on p.451 the authors explicitly leave normal convergence to
the reader. They do not present a separate `DifferentiableOn` theorem.
The holomorphy clause is the derived complex-analytic consequence for
this actual integral.

For a fixed quotient representative, put `d = |det g| > 0`. Its parameter
weight is `exp((s - (r-t)/2) log d)`, an entire function of `s`. For a
compact subset of the open half-plane, choose positive real endpoints
`a < b` whose strip contains a neighborhood of that subset. The
absolute integrand throughout the strip is bounded by the sum of the
absolute integrands at `a` and `b`: split into `d ≤ 1` and `d ≥ 1`.
Both endpoint functions are integrable by the convergence assertion.
The standard locally dominated holomorphic-parameter integral argument
therefore gives holomorphy. The zero-row measure has unit mass, so the
same argument applies to the existing nested integral. On the open
half-plane, holomorphy is expressed by `DifferentiableOn ℂ`.

This rationale explains the derived formulation; it is not an implemented
Lean proof. Establishing the restriction estimate, the source's convergence
argument, the coefficient-model and supplied-measure adapters, and the
holomorphic-parameter integration step remains separate proof work.
