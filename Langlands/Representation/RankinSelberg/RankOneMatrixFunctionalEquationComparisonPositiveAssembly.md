# Positive-rank assembly from a single-vector block-zero equation

This internal derived module works with the actual coefficient model of the
trivial rank-one representation and its identity functional. Its canonical
vector is the constant-one function. Every second vector equals its value at
the identity times this vector.

The original unequal-rank integral and the actual dual integral permit this
scalar to be absorbed into the first model vector. Both identities hold at
every spectral parameter without an integrability hypothesis, using
homogeneity of the totalized Bochner integrals. The dual identity retains the
complementary block, the inverse additive character, the unsigned long Weyl
function transform and the actual block Weyl right translate.

`unequalRankBlockZeroGammaEquation_rankOne_of_one` extends rational
continuations and a common gamma equation for this canonical second vector
to every second model vector. It uses the same absorbed first vector in
both continuations and transfers them by equality of the actual integrals.
Its nonzero block-zero value premise remains explicit.

For a canonical p-adic field, `rankOne_blockZero_exists_ne_zero` discharges
that nonzero-value premise for the supplied nonzero first functional. The
trivial rank-one representation is of inverse Whittaker type, with its
nonzero identity functional. The published `unequalRankUnitSpan` theorem
puts one in the rational span of the actual block-zero values. If all
those values vanished, their span would be zero, contradicting this
membership. This conclusion selects a nonzero rational continuation in
the actual value family; it does not claim convergence of every original
Whittaker integral.

For positive rank and the supplied self-dual scalar Haar measure,
`rankOneGammaFactor_of_blockZero_one` combines these facts with the
published `unequalRankGammaPropagation` theorem and
`unequalRankGammaFactor_of_equation`. Its input supplies, for every first
model vector, continuations of the actual original block-zero integral and
the genuine complementary dual integral, together with their common gamma
equation. Its conclusion is the full `IsPadicSymmetricGammaFactor`: the
same multiplier works at every block, every compatible quotient measure
and every pair of nonzero Whittaker functionals, with the existence clauses
of that predicate. The second model has scalar one at minus the identity,
so its factor in the functional equation is one.

`rankOneGammaFactor_of_normalized_blockZero_one` takes the normalized
block-zero equation with the supplied polynomials `P`, `PDual`, unit `c`
and integer `a`, and assumes `PDual ≠ 0`. The existing
`NormalizedFunctionalEquation.gamma_value_of_regular` gives the common
gamma equation on the full reduced-denominator domain for
`rationalGammaExpression (LocalFactor.residueReflection F) c a P PDual`.
The normalized sign exponent is zero; the equivalent rank-one central
scalar factor is one to the positive rank. The polynomial, measure and
gamma expression are unchanged.

These are internal derived consequences of the actual coefficient-model
definitions, integral homogeneity, unit-span theorem, block propagation and
the existing normalized-to-gamma identity. The field and representation
carrier universes remain independent. The analytic block-zero
continuations and equations remain explicit hypotheses. No matrix-to-block
extraction, unconditional convergence, or all-rank matrix comparison theorem
is asserted.

The canonical p-adic local instances have explicit
`matrixComparisonPositive` names. Their types, terms, order and locality are
unchanged. These names allow this assembly and the two-block L comparison
to be imported together without generated instance-name collisions.
