# Zero-row unequal-rank convergence, rationality and a common denominator

Worker 82, with target formulation by Worker 329.

The module defines the proposition
`Langlands.RankinSelberg.UnequalRankZeroRowAnalyticStatement.{uF,uV,uW} F T n k`.
It specializes the hypotheses of `UnequalRankAnalyticStatement F T n 0 k`
and retains exactly the first three clauses of its analytic conclusion.
The sole import is the published `AnalyticStatement`. This is a statement
target; neither its definition nor its publication proves the analytic claim.

## Data and scope

For every prime `p`, `F : PadicField.{uF} p` and supplied
`T : F.TopologicalData`, the statement installs precisely the local instances
of the parent target: `T.topology`, `T.valuativeRel`, `T.localField`, the
Borel measurable structure on `F.Carrier`, and the Borel structures and
`BorelSpace` instances on the smaller general linear group, its upper
unipotent subgroup, and its left-unipotent quotient.
The data `T` are supplied independently of the canonical choice.

Every nontrivial continuous unitary additive character `ψ` is quantified
through `UnitaryAdditiveCharacter`. The statement retains the explicit
right-invariance instance for `unipotentHaar F.Carrier n`. It quantifies
every measure `μ` on `LeftUnipotentQuotient n F.Carrier` satisfying
`QuotientIntegration.IsCompatible` for the published normalized group and
unipotent Haar measures, and every `ν : AdditiveHaarMeasure F.Carrier`.
No self-dual normalization is imposed.

The representation carriers `V : Type uV` and `W : Type uW`, with their
complex module structures, are quantified independently of the field
universe `uF` and of each other. The larger representation `π` has rank
`n + (0 + k + 1) + 1`; the smaller representation `σ` has rank `n + 1`.
The unreduced larger-rank spelling matches the existing block interface
exactly, so no rank transport is required. Both `n` and `k` are arbitrary
natural numbers: `n = 0` includes a rank-one smaller group, `k = 0`
includes corank one, and general `k` gives rank gap `k + 1`.

The two representations are of Whittaker type for the standard and inverse
standard characters, respectively. This is the parent's full admissible,
finitely generated group-algebra module scope with a one-dimensional
Whittaker functional space. It includes reducible representations. Every
pair of nonzero functionals `ℓ` and `ℓ'` is quantified, and the functions
are elements of their actual coefficient images. There are no added
irreducibility, unitary central character, torus estimate, decomposition,
convergence, rationality or denominator hypotheses.

## Integral and three conclusions

Write `q = T.residueCardinality` and use `normalizedAbsoluteValue T`.
In source notation the ranks are `t = n + 1` and
`r = n + (0 + k + 1) + 1`. The zero-row block is the diagonal restriction
`diag(g, 1_(k+1))`. Its determinant weight has exponent
`s - (k + 1)/2`, retaining the full rank gap.

The statement uses the existing rectangular product measure
`rectangularMeasure ν 0 (n + 1)`, convergence predicate, nested integral
and rational-value set without introducing replacements.
`rectangularMeasure_zero_rows` identifies this measure with `Measure.dirac 0`,
but the proposition keeps the original product-measure and nested-integral
interfaces.

1. For every pair `f`, `f'` in the coefficient models, there is a real
   bound `a` such that `UnequalRankConverges` holds whenever `a < s.re`.
   This asserts joint absolute integrability on the quotient times the
   zero-row matrix space under
   `μ.prod (rectangularMeasure ν 0 (n + 1))`. The bound may depend on the
   pair. It is stronger than merely writing down the totalized integral.
2. For every such pair there exists `R : RationalFunctions` satisfying
   `HasRationalContinuation q` for the actual `unequalRankModelIntegral`.
   That integral first integrates the rectangular variable and then the
   quotient variable. The continuation relation requires both equality
   with `R(q^(-s))` and nonvanishing of its denominator on a right half-plane.
3. `HasCommonDenominator` holds for the entire existing set
   `unequalRankRationalValues 0 k q ψ ... π σ ℓ ℓ'`.
   Concretely, a single nonzero Laurent polynomial `d` clears every rational
   value in that set: for every such `R`, some Laurent polynomial `b`
   satisfies `laurentToRatFunc b = laurentToRatFunc d * R`.
   The denominator is chosen once for all coefficient-model function pairs
   at the fixed preceding data; it is not separately chosen for each pair.
   No uniform choice across different representations, ranks, characters,
   measures or functionals is asserted.

The common denominator is a distinct conclusion, not a consequence assumed
from pointwise rationality. Normalized-generator existence, membership of
one in the Laurent span, and block-independent generators are outside this
target.

## Original source and remaining proof prerequisites

Source: H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg convolutions*, American Journal of Mathematics 105 (1983),
367–464; registered as `jpss-1983-rankin-selberg`.
The retained original PDF has SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pages 388–394 were read visually; their zero-based PDF indices
are 22–28.

Section 2.5, pp.388–389, supplies the finite-function torus expansion
and majorization route. Theorem 2.7(i)–(ii), pp.390–391, states absolute
convergence and rationality with the fractional-ideal conclusion for
representations of Whittaker type. Its proof on pp.391–392 uses Iwasawa
integration, compact-group finiteness, torus expansions and products of
one-variable Mellin integrals. The finite families depend on the
representations, while the Schwartz functions vary with the vectors;
this is the source of the denominator's uniformity.

For unequal ranks, pp.393–394 reduce the rectangular integral to a finite
sum of diagonal restriction integrals. Equation (7) on p.394 is precisely
the integral with `W(diag(g, 1_(r-t)))`, `W'(g)`, and determinant exponent
`s - (r-t)/2`. The following paragraph applies the preceding torus
argument to obtain convergence and rational functions with a fixed
denominator. The present formulation isolates that analytic subcase.
For a general block `(j,k)`, its zero-row reduction has remaining parameter
`j+k`, preserving the larger rank and exponent after the relevant
natural-number type transport.

Section 2.5 explicitly introduces its expansion in generic language and
its initial gauge bound with a unitary-central-character assumption.
Theorem 2.7 itself has the broader Whittaker-type scope retained here.
Formal proofs of the full Whittaker-type torus expansions and majorants,
their supplied-topology and coefficient-model adapters, quotient Iwasawa
integration, and finite-function Mellin convergence, rationality and
uniform denominators remain prerequisites. They are not assumptions
inserted into this proposition, nor results proved by defining it.
The compact-support and finite block reduction and the later
normalized-generator arguments are separate steps.

## Lean validation

The exact proposition was compiled and inspected in the prepared Lean
environment. Inspection reports `statement_returns_prop = true`, independent
universe parameters `uF`, `uV`, `uW`, and only `propext`, `Classical.choice`
and `Quot.sound`. Compilation produced no errors or warnings. This check
validates the definition and does not prove its analytic assertion.
