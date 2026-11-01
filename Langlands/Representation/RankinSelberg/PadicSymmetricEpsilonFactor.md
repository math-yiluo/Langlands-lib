# Constructed generic p-adic epsilon factors in either rank order

Author: Worker 31.

`genericPairEpsilonData`, `genericPairEpsilonFactor` and
`genericPairEpsilonValue` construct coefficient/exponent data in `ℂˣ × ℤ`,
a unit of `RatFunc ℂ`, and a complex unit at each complex spectral
parameter. They apply to generic representations of `GL_(r+1)` and
`GL_(n+1)` with `n ≤ r`. `genericSymmetricEpsilonData`,
`genericSymmetricEpsilonFactor` and `genericSymmetricEpsilonValue` apply
to either rank order. All ranks are positive, with rank one included in
both slots; the field and two representation carriers have independent
universes.

The topology, normalized absolute value and residue cardinality `q` are
canonical for the p-adic field. The inputs include a nontrivial unitary
additive character and an additive Haar measure satisfying the existing
plus-Fourier `IsSelfDual` predicate. The measure is supplied. Each
`Whittaker.IsGeneric` hypothesis means irreducibility, admissibility and
existence of a nonzero standard Whittaker functional. The equal and
unequal constructors provide the inverse-character full type needed in
the second slot through the existing generic-model bridges.

The original source is Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg Convolutions* (1983), registered as
`jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Theorem 2.7(iii), printed p.391, displays (1) and (2), supplies the
equal and unequal normalized equations with a nonzero monomial
`c q^(-ms)`. Section 2.12, printed p.403, defines the opposite-order
epsilon factor for unequal ranks to equal the larger-first factor.
The implementation uses exactly that convention, retaining the
original pair at equality.

`genericPairEpsilonFactorExists` splits `n ≤ r` into strict inequality
and equality. In the first case it uses
`genericUnequalRankEpsilonData_isPadic`; in the second it identifies
the ranks and uses `genericEqualRankEpsilonData_isPadic`. These
constructors obtain the full integral relation from the respective
proved functional equations. In particular, a compatible quotient
measure and nonzero functionals exist, and the same coefficient and
exponent work for all compatible measures, nonzero functional pairs
and all unequal-rank blocks.

`genericPairEpsilonData` chooses from that proved existence, and its
specification is exactly `IsPadicPairEpsilonFactor` for the original
representations. Its equality theorem compares the chosen data with
every certified pair using the existing uniqueness theorem. Further
comparison theorems identify the data with the strict unequal-rank
constructor or the equal-rank constructor in the respective cases.

`genericSymmetricEpsilonData` uses the ordered constructor on `(π,σ)`
when `n ≤ r`, and on `(σ,π)` otherwise. Its specification is exactly
the existing `IsPadicSymmetricEpsilonFactor`, transported through
the published rank-order equivalences. The relation has the complete
measure and functional witnesses above, and the uniqueness theorem
compares the result with every other certified pair. The branch
comparisons state the actual selected data in both orders.

Both rational-function constructors form `rationalEpsilonMonomial`
from their selected data. Their coercions are exactly `C(c) * X^m`
with `X=q^(-s)`, and their characterization theorems identify the
unit with the monomial for any certified data. The symmetric
constructor agrees with the ordered factor in each branch.

Both spectral constructors use `Units.mk0` on the same
`epsilonMonomial q c m s`. The proved `1 < q` implies positive `q`;
the existing monomial nonvanishing theorem then supplies the unit
proof for every `s : ℂ`. Their coercion and characterization
theorems give exactly `c * (q^(-s))^m`. These are rational and spectral
formulas; no general rational-function evaluation theorem is added.

This is derived assembly of
[PadicEqualRankEpsilonFactor](PadicEqualRankEpsilonFactor.md),
[PadicUnequalRankEpsilonFactor](PadicUnequalRankEpsilonFactor.md),
[PairEpsilonFactor](PairEpsilonFactor.md) and
[PadicPairFactors](PadicPairFactors.md). The private structural
helper derives the nonarchimedean additive structure from the
valuation-topology open-submodule basis, as in the imported
constructions. No analytic, functional-equation, epsilon-existence
or quotient-measure premise is added to these constructors.

The larger-first convention does not establish the equal-rank
interchange law. Change of additive character, twist laws, gamma
factors and classification-based nongeneric factors remain
separate results.
