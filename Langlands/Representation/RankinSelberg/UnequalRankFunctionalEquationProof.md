# The uniform unequal-rank normalized functional equation

Author: Worker 103.

The theorem `Langlands.RankinSelberg.unequalRankFunctionalEquation` proves
exactly `UnequalRankFunctionalEquationStatement.{uF,uV,uW} F T n r` from
`FunctionalEquationStatement`. It quantifies every prime, p-adic field,
supplied topology and pair of rank parameters, retaining independent universes
for the field and the two representation carriers. Its hypotheses are precisely
those of that published proposition, including the full Whittaker-type scope.

For fixed representation and measure data with `n < r`, the conclusion chooses
one model-minus-one scalar `ζ`, one unit `c`, one integer `m`, and normalized
polynomials `P`, `Pdual` before every allowed block and coefficient pair.
The epsilon monomial is `c * (q^(-s))^m`. The sign exponent is `r` for the
larger rank `r + 1`. The dual integral retains the complementary block `k`,
the inverse additive character, inverse-transpose models and right translation
by the actual `blockWeylAt n r`. Both rectangular measures use the same supplied
self-dual scalar Haar measure. The equation holds on the exact denominator
domain of `NormalizedFunctionalEquation`.

## Implemented proof

The proof imports and applies the Library theorems
`unequalRankCommonGenerator`, `unequalRankBlockZeroGammaExistence`,
`unequalRankGammaPropagation` and `gammaNormalization` by their Lean names.
Their propositions are discharged by these proofs; they are not additional
hypotheses of the final theorem.

The common-generator theorem is applied first to the given pair, then to its
inverse-transpose pullbacks with character `ψ.scale (-1)`. The published
Whittaker-type transport theorems preserve the full representation scope, and
`firstDualFunctional_ne_zero` and `secondDualFunctional_ne_zero` preserve the
nonzero specified functionals. Both applications use the same quotient measure
and scalar Haar measure. The common-generator theorem does not require
self-duality of the latter, so no new inverse-character measure hypothesis is
needed.

The private lemma `dualUnequalRank_commonGenerator_of_inverseTranspose` uses
`dualUnequalRankRationalValuesAt_eq` to identify the actual dual value family
with the inverse-transpose family at exchanged blocks `k, j`. This equality
already accounts for the right translation by the block Weyl matrix.
It transports the second common polynomial to every dual block.

The block-zero gamma theorem supplies a nonzero rational multiplier `G` for
all coefficient pairs at block zero. The propagation theorem uses that same
`G` to provide `UnequalRankGammaEquation` for every block, with the supplied
measures and the actual transformed tests.

The private lemma
`unequalRankFunctionalEquationConclusion_of_common_generators` performs the
remaining algebraic assembly. At block zero it proves both incidence
conditions required by `gammaNormalization`. Every original rational
continuation comes from a coefficient pair; the gamma equation supplies the
paired dual continuation. Conversely, every dual continuation comes from a
coefficient pair to which that equation applies.
`HasRationalContinuation.unique`, using `1 < q`, identifies any previously
specified continuation with the corresponding one from the gamma equation.

The two incidence conditions and normalized generators give one unit `c` and
integer `m` through `gammaNormalization`. That theorem applies to every
rational pair satisfying the same gamma equation. Thus the same `c`, `m`,
`P` and `Pdual` work at every block. It supplies the normalized equation on
the denominators of the original and dual continuations alone; no extra
restriction from a denominator of `G` is added. The nonvanishing of `G`
is provided by the block-zero theorem but is not needed separately in this
assembly.

The private `valuative_nonarchimedean` helper repeats the valuation-topology
bridge used by the published statement. Mathlib's open-submodule basis supplies
the nonarchimedean additive structure needed to elaborate the same self-dual
measure telescope. This is derived typeclass data, with no added hypothesis.

## Provenance

This module is an internal assembly of JPSS Theorem 2.7(iii), display (2),
printed p. 391. The uniformity in the block is the content of section 2.8,
p. 395; the passage to a normalized epsilon monomial follows section 2.9,
pp. 395–396; block-zero existence is proved in section 2.11, pp. 398–403.
The implementation reuses the Library proofs of these ingredients and the
common-generator theorem rather than duplicating their analytic or uniqueness
arguments. The private incidence and transport lemmas organize this assembly
and make no additional source assertion.

Registered original: `jpss-1983-rankin-selberg`, Jacquet, Piatetski-Shapiro and
Shalika, *Rankin-Selberg Convolutions*, American Journal of Mathematics 105
(1983), 367–464, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The original passages needed for this assembly were read in the earlier
source investigation recorded in this task.
