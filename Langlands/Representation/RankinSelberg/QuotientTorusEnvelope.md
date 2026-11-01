# Summable torus envelopes on the standard quotient

This internal derived module connects the published normalized quotient Iwasawa
formula with a summable majorant for a measurable complex function. It retains
every supplied compatible quotient measure and uses the exact inverse upper-Borel
modulus. It supplies an analytic bridge for the Section 4.7 fixed-slice proof;
it does not assert the concrete representation bounds or prove the full host
convergence proposition.

## Weighted probability pushforwards

For a countable family of measurable maps `q l` from a probability space with
measure `nu`, suppose `E` is a measurable complex function and
`norm (E (q l x)) <= A l` almost everywhere for each `l`. Let `c l` be
nonnegative real weights. If `sum_l c l * A l` is summable, then
`integrable_sum_smul_map_of_bound` proves that `E` is integrable for

`Measure.sum (fun l => ENNReal.ofReal (c l) * Measure.map (q l) nu)`,

where the multiplication in this display denotes scalar multiplication of a
measure. The theorem assumes no separate sign condition on `A`: the norm bound
on a probability space already excludes a negative bound.

The implemented proof first uses almost-everywhere boundedness to obtain
integrability of every pullback on the probability space. The pushforward
criterion gives integrability for each mapped measure, and multiplication by a
finite scalar gives it for each weighted mapped measure. The integral of the norm
for that measure equals `c l` times the norm integral on the probability space,
which is at most `c l * A l` because its total mass is one. The comparison test
makes these norm integrals summable. Mathlib's `integrable_sum_measure` then gives
absolute integrability for their countable sum. This argument uses genuine
integrability throughout.

`sumPushforwardL1` constructs the actual `L1` class of the supplied `E` for this
weighted sum measure by applying `Integrable.toL1` to that proved result.
`sumPushforwardL1_coe` identifies its representative with `E` almost everywhere
for exactly that measure.

## The standard unipotent quotient

For a p-adic field `F`, its supplied topological data `T`, a positive matrix rank
`n+1`, and a unit uniformizer `varpi` with the required valuation, `density` is

`(prod_i prod_{j>i} T.normalizedAbs (varpi^(lam i) / varpi^(lam j)))^(-1)`.

It is the literal reciprocal of the upper-Borel modulus evaluated at the
uniformizer powers. Every argument of the absolute value is a unit, so the finite
product and its reciprocal are strictly positive, as proved by `density_pos`.

`quotientMeasure_eq_sum_torus` composes the published
`quotientIwasawaIntegration` and `iwasawaTorusSum` identities. Every measure `mu`
compatible with the prescribed general linear Haar and unipotent Haar measures
therefore equals the countable sum over all integer exponent vectors `lam` of

`ENNReal.ofReal (density F T varpi lam)` times the pushforward, under
`k |-> [Iwasawa.torus varpi lam * k]`, of general linear Haar restricted to the
canonical integral subgroup. No quotient measure is replaced by a chosen one.
The right invariance of the prescribed unipotent Haar measure is an explicit
instance hypothesis inherited from the published quotient integration formula.
All measurable structures here are the Borel structures of `T` and the actual
quotient topology.

`integrable_of_summable_torus_bound` applies the generic lemma to this identity.
The restricted compact Haar measure has mass one by
`generalLinearHaar_integralSubgroup`. The integral subgroup is measurable because
it is the level-zero open subgroup, so a pointwise bound for every `k` in it gives
the needed almost-everywhere bound for the restricted measure. Left multiplication
and the quotient map are continuous, hence the compact pushforward maps are
measurable. Consequently a measurable `E` is integrable for every compatible
`mu` whenever its norm at these torus representatives is bounded by `A lam` and
`density F T varpi lam * A lam` is summable. The assertion permits a measurable
slice indicator as the function `E`; ordinary restriction of a globally integrable
function also gives integrability on each slice.

## Provenance and scope

All assertions are derived from the existing normalized measure identities,
canonical Haar normalization, and Mathlib's measure and Bochner integral results.
There is no new claim about original literature and no use of convergence,
Whittaker irreducibility, a functional equation, or multiplicativity as a premise.
The field universe is arbitrary; the probability-space lemma has independent
index, source, and target universes. The representation-dependent threshold,
concrete norm bounds, endpoint support and summability estimates belong to the
other units of the host proof.
