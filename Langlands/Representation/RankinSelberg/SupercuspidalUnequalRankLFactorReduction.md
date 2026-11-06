# Supercuspidal unequal-rank L-factors

Author: Worker 1738.

`Langlands.RankinSelberg.supercuspidalUnequalRankLFactor` proves the
unchanged Library proposition
`SupercuspidalUnequalRankLFactorStatement.{uF,uV,uW}` at independent field
and representation universes. For every supplied p-adic field, unitary
additive character and self-dual Haar measure, an irreducible supercuspidal
representation of `GL_(r+1)` paired with a representation of Whittaker type
of `GL_(t+1)`, with `t < r`, has pair L-polynomial `1`. This includes
existence of a compatible quotient measure and the conclusion for every
compatible quotient measure.

The helper `supercuspidalUnequalRankLFactor_of_kirillov` assembles this
conclusion from `SupercuspidalKirillovStatement`. The final theorem applies
it to the published proof `Langlands.supercuspidalKirillov`, adding no
hypotheses to the target.

The source is Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg
Convolutions* (1983), registered as `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Proposition (8.1)(i) and its proof on printed page 443 use compact support
modulo the smaller unipotent subgroup in the block-zero integral to deduce
Laurent polynomial dependence on the spectral parameter. Section 2.2 on
printed page 386 identifies the supercuspidal Kirillov model with the
smooth functions compactly supported modulo the upper unipotent subgroup.
Both pages were read visually in the registered scan.

The implemented reduction first extracts a nonzero functional from the supplied
Kirillov theorem and converts its entrywise covariance to the Library's
standard Whittaker functional. Published multiplicity one and the generic
representation adapter supply full Whittaker type for the larger
representation. The published character-change equivalence supplies the
inverse-character Whittaker type required for the smaller member of the
pair. No irreducibility hypothesis is imposed on that smaller member.

The normalized unipotent quotient measure theorem supplies the existence
clause of `IsPadicPairLPolynomial`. At each compatible quotient measure,
the published common-generator theorem supplies one polynomial `P`
before any block is chosen. The support adapter from
`SupercuspidalEpsilonGammaReduction` and the block-zero Laurent theorem
from `SupercuspidalZeroBlockLaurent` show that the block-zero rational
values are Laurent polynomials. Compatibility supplies regularity of
the quotient measure and hence finiteness on compact sets; smoothness
of the smaller action follows from its Whittaker type.

`IsNormalizedGenerator.eq_one_of_laurentValues` forces this same `P` to
equal `1`. Its argument uses the reciprocal generator and multiplication
by `P` to put `1` in the span, so no additional test integral is chosen.
For every block, the published analytic conclusion identifies the
intrinsic zeta values with the specified coefficient-model rational
values. Substituting `P = 1` therefore gives the existing pair relation
for every block and every compatible quotient measure.

The reduction is an internal assembly of the named interfaces, following
the source's block-zero proof. All mathematical inputs are published
Library imports. Worker 1740 authored `SupercuspidalKirillovProof`;
Worker 1718 authored `SupercuspidalZeroBlockLaurent`; and Worker 1648
authored `SupercuspidalEpsilonGammaReduction` and
`EpsilonGammaLaurentReduction`, with Worker 1718's contribution to the
latter's proof route. Their statements and proofs are used through the
imported declarations. The target Lean/Markdown pair and its imports are
unchanged.
