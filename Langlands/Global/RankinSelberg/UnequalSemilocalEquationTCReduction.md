# A conditional proof of the unequal-rank semi-local functional equation over totally complex fields

`Langlands.Global.RankinSelbergGlobal.UnequalSemilocalEquationTCReductionStatement.{u, uQ}`
is the Prop-valued statement

`UnequalSemilocalFactorizationTCStatement.{u, uQ} → UnequalSemilocalEquationTCStatement.{u, uQ}`.

The module proves it as `unequalSemilocalEquationTCReduction`, by the theorem
`unequalSemilocalEquationTC_of_factorizationTC`.

* `UnequalSemilocalEquationTCStatement` is the totally complex form of
  `UnequalSemilocalEquationStatement`. It is defined in the published module
  `Langlands.Global.RankinSelberg.SemilocalEquationTCStatements`.
* The premise `UnequalSemilocalFactorizationTCStatement` is the totally complex form of
  `UnequalSemilocalFactorizationStatement`. It is defined in the module of the same name,
  and it remains open.

This is therefore a conditional result. It does not prove
`UnequalSemilocalEquationTCStatement`. The proofs use only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Source

J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004),
`cogdell-2004-analytic-theory-gln` (PDF page = printed page + 3): the proof of Theorem 4.1,
printed pp.219–220. The local functional equations at the places of `S` are Theorem 3.2
(p.214). In the reduction they come from the Library rather than from the premise.

## Proof

The proof is the published proof of `unequalSemilocalEquation_of_factorization` (module
`Langlands.Global.RankinSelberg.UnequalSemilocalEquationReduction`), repeated with one
change. The target's binders now include the instance `[NumberField.IsTotallyComplex F]`,
and the premise is applied at the same field `F`. At that point the instance is in
context, so the totally complex premise applies. The published theorem takes the premise
for every number field, so it cannot be applied to the weaker totally complex premise
directly. That is why its proof body is repeated here, rather than the theorem being
called.

The module imports the published reduction module and uses its helper lemmas in the
namespace `UnequalSemilocalReduction`:

* `canonicalFiniteAdditiveComponent_unique`;
* `PadicUnequalTestData.exists_gammaEquation`;
* `rdual_ne_zero`;
* `meromorphicOn_eval_spectralPoint`;
* `eventually_eval_ne_zero`, `eventually_denom_ne_zero` and
  `eventually_denom_reflected_ne_zero`.

It also uses the same Library results as the published proof:

* `canonicalFiniteAdditiveComponent`;
* `Correspondence.localSelfDualHaar` and `eq_localSelfDualHaar`;
* `Automorphic.CuspidalPairPartialGamma.localGenericity`;
* `RankinSelberg.genericPairGammaFactor_isPadic`;
* `RankinSelberg.isPadicSymmetricGammaFactor_of_le`;
* `HasRationalContinuation.unique`.

The steps, in outline, follow. The Markdown of the published reduction gives them in
detail.

1. Apply the premise to the canonical finite components `ψ0` of `ψ` and their self-dual
   measures `ν0`. This gives `x`, `x'`, `σ0`, `Ainf`, `Binf`, the local data `D v` at
   `v ∈ S`, and nonzero continuations `R_v` of the local integrals.
2. At each `v ∈ S`, take a nonzero local gamma factor `G0_v` of the generic local
   components. The gamma functional equation of the data gives a continuation `Rd_v` of
   the dual local integral, and `Rd_v ≠ 0`.
3. Set `A(s) = Ainf(s) ∏_(v ∈ S) R_v(q_v^(−s))` and
   `B(s) = Binf(s) ∏_(v ∈ S) Rd_v(q_v^(−s))` on a common right half-plane. These are
   meromorphic, nonzero off a discrete set, and equal to the partial integrals there.
4. For given `ψv`, `νv` and `G`, uniqueness gives `ψv = ψ0` and `νv = ν0`. The local gamma
   functional equations, multiplied over `S` and combined with the sign clause of the
   premise, give
   `L_∞(s) B(1 − s) = (∏_(v ∈ S) G_v(q_v^(−s))) ε_∞(s) L∨_∞(1 − s) A(s)` off a discrete set.

The argument does not use the totally complex hypothesis anywhere except to apply the
premise. It works verbatim because the premise and the target have the same `infiniteL`,
`dualInfiniteL` and `infiniteEpsilon`. The module declares the same two local instances
as the targets (`GroupScheme.GeneralLinear.isAffine_groupScheme`,
`GroupScheme.GeneralLinear.smoothStatement`).

## Provenance

Internal intermediate result of Task 7053, under its "Intermediate results" clause.
Worker 0 (Task 0 coordinator) asked for it after operator answer
`81ed24709e7050068786116ca6613260` (Option A). That answer restricts Task 0's global
chain to totally complex base fields. The argument is Cogdell's (pp.219–220).
