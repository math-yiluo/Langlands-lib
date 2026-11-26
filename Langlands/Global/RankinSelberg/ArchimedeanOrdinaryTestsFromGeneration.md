# Ordinary archimedean tests from local generation and restriction surjectivity

Module `Langlands.Global.RankinSelberg.ArchimedeanOrdinaryTestsFromGeneration`, namespace
`Langlands.Global.RankinSelbergGlobal`. The module
[`ArchimedeanFactorizationOrdinaryReduction`](ArchimedeanFactorizationOrdinaryReduction.md)
reduces `ArchimedeanFactorizationStatement` to a slice comparison, the real-place functional
equation and four statements of ordinary nonvanishing on actual archimedean restrictions. This
module derives the four ordinary statements from two local inputs at each kind of place. These
are normalized generation in the local Whittaker models, and the fact that every function of
such a model is an actual restriction. It proves the derivations; it proves neither input.

## Two new statements: restriction surjectivity for every realization

`RealPlaceWhittakerRestrictionOntoStatement` has these hypotheses:

- a number field `F` with `AdeleQuotient F` compact;
- a unitary additive character `ψ` of the adeles trivial on `F`;
- an actual cuspidal realization `T` of `GL_(r+1)`;
- a real place `v` and the scale `a ∈ ℝˣ` of the component of `ψ` at `v`;
- a parameter list `d` of `T` at `v` (`HasRealPlaceParameter`).

It asserts, for every function `W` on `GL_(r+1)(ℝ)`:

- if `W ∈ realWhittakerModel r d a`, then `W` is an actual restriction of a global Whittaker
  function of `T` for `ψ` (`IsRealPlaceWhittaker F T ψ.complex v W`);
- if `W ∈ realWhittakerModel r d (-a)`, then the same holds for `ψ⁻¹`.

`ComplexPlaceWhittakerRestrictionOntoStatement` is the same assertion at a complex place,
with `complexWhittakerModel`, `HasComplexPlaceParameter` and `IsComplexPlaceWhittaker`.

These are the published `RealPlaceWhittakerRestrictionSurjectivityStatement` and
`ComplexPlaceWhittakerRestrictionSurjectivityStatement` (module `CuspidalPairPoleLocalRanges`)
without their hypothesis `IsTrivialOnSplitCentre T`. They imply the published statements
directly. The reverse inclusion, that actual restrictions lie in these models, is the
published `archimedeanPlaceWhittakerModels` (module `ArchimedeanPlaceWhittakerModels`),
followed at real places by `RealUniformWhittaker.model_le_model`.

## Results

**Nonzero models.** `realWhittakerModel_ne_bot` and `complexWhittakerModel_ne_bot`: for an
actual cuspidal realization `T` with parameter `d` at the place and the scale `a` of `ψ` there,
the models for `a` and for `-a` are both nonzero. By `cuspidalWhittakerIdentityNonzero`
(module `CuspidalWhittakerIdentityNonzero`) some vector `x` has global Whittaker function
nonzero at the identity, for `ψ` and also for `ψ⁻¹`; the inverse character is standard by
`UnramifiedWhittaker.isStandardAdditiveCharacter_complex` applied to `inverseCharacter ψ`. The
restriction `g ↦ W_x(ι_v(g) · 1)` is nonzero at `g = 1`, since `ι_v(1) · 1` is the identity
adelic point. It lies in the model by the published forward comparison.

**Local tests.** Four theorems, `exists_realUnequalOrdinaryTest`,
`exists_realEqualOrdinaryTest`, `exists_complexUnequalOrdinaryTest` and
`exists_complexEqualOrdinaryTest`, take the following data:

- the corresponding generation statement;
- actual cuspidal realizations `T` of `GL_(r+1)` and `T'` of `GL_(t+1)`, with `t < r` in
  unequal rank and `t = r` in equal rank;
- their parameter lists `d`, `d'` at the place;
- two surjectivity hypotheses for these data only: every function of the model of `d` for `a`
  is an actual restriction of `T` for `ψ`, and every function of the model of `d'` for `-a` is
  an actual restriction of `T'` for `ψ⁻¹`.

They conclude the bodies of the four ordinary statements. That is, there are actual
restrictions `W` of `T` for `ψ` and `W'` of `T'` for `ψ⁻¹`, quotient measure data `D` and, in
equal rank, a Schwartz function `Φ`, such that the ordinary integral is nonzero at points
arbitrarily far to the right.

The proof applies the generation statement with the following inputs:

- `realRank d = r + 1`, resp. `d.length = r + 1`, from the parameter;
- irreducibility of the two standard modules, by
  `CuspidalOperatorRealization.isIrreducibleRealStandard`, resp.
  `isIrreducibleComplexStandard`;
- the Library's quotient measure data `realQuotientMeasureData`, resp.
  `complexQuotientMeasureData`;
- the nonzero models above.

The covering clause of the generation statement, used only at `s = 0`, gives a model test with
ordinary integral `Z` and an entire normalization `N` with `N.value 0 ≠ 0`. By the definition of
`OrdinaryIntegralNormalization`, on some right half-plane

`Z(s) = N.value(s) · L(s)`, where `L(s) = (pairDenominator(s))⁻¹`

is the reciprocal of the denominator of the pair L-factor (`realPairLFactor d d'`, resp.
`complexPairLFactor d d'`). The published `OrdinaryIntegralNormalization.exists_ne_zero_above`
(module `UnequalPlaceTestsFromOrdinary`) then finds, to the right of any given bound and of that
half-plane, a point `s` at which both `N.value(s)` and `pairDenominator(s)` are nonzero. Both are
entire and not identically zero, so each vanishes only on a discrete set. At such a point the
product `N.value(s) · pairDenominator(s)⁻¹ = Z(s)` is nonzero. The surjectivity hypotheses
identify the two test vectors as actual restrictions.

**Ordinary statements.** `realOrdinaryPlaceTests_of_generation` derives
`RealUnequalOrdinaryPlaceTestsStatement` and `RealEqualOrdinaryPlaceTestsPositiveRankStatement`
from `RealOrdinaryNormalizedGenerationStatement` and
`RealPlaceWhittakerRestrictionOntoStatement`. `complexOrdinaryPlaceTests_of_generation` derives
the two complex statements from the complex generation and surjectivity statements. Each one
instantiates the local tests.

**Conditional factorization.**

```
def ArchimedeanFactorizationGenerationReductionStatement : Prop :=
  InfiniteWhittakerSliceModelStatement.{u, uQ} → RealPlaceFunctionalEquationStatement.{u} →
    RealOrdinaryNormalizedGenerationStatement → ComplexOrdinaryNormalizedGenerationStatement →
    RealPlaceWhittakerRestrictionOntoStatement.{u} →
    ComplexPlaceWhittakerRestrictionOntoStatement.{u} →
    ArchimedeanFactorizationStatement.{u, uQ}
```

`archimedeanFactorizationGenerationReduction` proves it. It applies
`archimedeanFactorizationOrdinaryReduction` to the four ordinary statements obtained above.
The proofs use only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

Internal. The generation statements are Library formulations of consequences of H. Jacquet,
*Archimedean Rankin–Selberg integrals* (2009), Theorems 2.3, 2.6 and 2.7, pp. 8–10.
Theorem 2.3 gives continuous maps from the Whittaker coefficient data (with a Schwartz function
in equal rank) into Jacquet's space `L(σ_u ⊗ σ'_u')` (pp. 5–6), whose members are holomorphic
multiples of the L-factor, and the discussion on pp. 8–9 extends the integrals to completed
projective tensor products. Theorem 2.6 realizes a
prescribed member of that space, for ordered inducing exponents, by a completed-tensor test in
unequal rank, or by a sum of completed-tensor tests with Schwartz functions in equal rank.
Theorem 2.7 writes the L-factor as a finite sum of integrals of compact-finite algebraic tensors
of irreducible induced modules, in equal and adjacent ranks, with standard Schwartz tests in
equal rank. Passing from these to pointwise covering by individual model tests in all ranks
needs continuity of normalized evaluation, density of elementary tensors and a comparison of
Jacquet's models with the Library's specified models. This module takes the generation
statements as hypotheses and uses only their covering clause at `s = 0`.

The surjectivity statements identify the space of actual restrictions with the Whittaker model
of the archimedean component of the cuspidal representation. A test with nonzero integral for
"appropriate" vectors at the infinite places is the step used in J. W. Cogdell, *Analytic
theory of L-functions for GL_n* (2004), proof of Theorem 4.1, printed pp. 219–220.
