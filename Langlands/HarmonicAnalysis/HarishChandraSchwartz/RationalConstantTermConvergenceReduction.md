# Radical convergence and the vanishing comparison from Proposition II.4.5

Author: Worker 762, task `79ac4c17-fe39-4c1c-bb7f-f0d531569c87` (Task 7438, revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConstantTermConvergenceReduction`,
namespace `Langlands.HarishChandraSchwartz`.

## Purpose

Task 7438 asks for proofs of three closed propositions of the module
`RationalCuspidalConvergenceStatements`:

1. `RationalSchwartzCentralConvergenceStatement` (absolute convergence of the central integrals);
2. `RationalSchwartzConstantTermConvergenceStatement` (integrability of `v ↦ f(x v y)` on every
   standard unipotent radical `U_J(F)` with `J` proper, for every actual Schwartz function `f`);
3. `RationalCuspidalVanishingComparisonStatement` (the cuspidal submodule is cut out by the
   vanishing of the normalized standard constant terms alone).

Their inputs are published Library propositions whose proofs are not yet available. This module
and the module `RationalCuspidalConvergenceReductions` reduce each target to these propositions,
named as hypotheses, so that the final proofs are applications:

| Target | Reduction | Hypotheses |
| --- | --- | --- |
| 1 | `RationalSplitCenterHeightStatement.schwartzCentralConvergence` (module `RationalCuspidalConvergenceReductions`) | `RationalSplitCenterHeightStatement` |
| 2 | `RationalConstantTermEstimateStatement.schwartzConstantTermConvergence` (this module) | `RationalConstantTermEstimateStatement`, `JointSpecialCompactBasisExistenceStatement` |
| 3 | `RationalConstantTermEstimateStatement.cuspidalVanishingComparison` (this module) | `RationalConstantTermEstimateStatement`, `JointSpecialCompactBasisExistenceStatement` |

The hypotheses are the published statements of Task 5480 (`RationalSplitCenterHeightStatement`,
module `RationalCentralProjection`), Task 5460 (`RationalConstantTermEstimateStatement`,
Waldspurger's Proposition II.4.5 on actual points, module `RationalConstantTerm`) and Task 4169
(`JointSpecialCompactBasisExistenceStatement`, module `BruhatTits.SpecialCompact.JointBasisStatement`).
This module proves no part of them and no target unconditionally.

## The recorded proposition

`RationalConstantTermConvergenceReductionStatement : Prop` (universe `u`) is the implication

`RationalConstantTermEstimateStatement.{u} → JointSpecialCompactBasisExistenceStatement.{u} →
RationalSchwartzConstantTermConvergenceStatement.{u} ∧ RationalCuspidalVanishingComparisonStatement.{u}`.

It is proved in the same module by `rationalConstantTermConvergenceReduction`, which pairs the two
theorems below. It is a reduction between published propositions, not a statement from the
literature.

## Results

### `RationalConstantTermEstimateStatement.schwartzConstantTermConvergence`

`(h : RationalConstantTermEstimateStatement.{u}) (hJoint : JointSpecialCompactBasisExistenceStatement.{u}) :
RationalSchwartzConstantTermConvergenceStatement.{u}`.

Proof. Fix the data of the target: `F`, a connected reductive `G`, a maximal split torus `i`, a
generic cocharacter `ν`, a compact open `K` with `G(F) = P₀(F) K`, a closed matrix representation
`ρ`, a Schwartz function `f` for `Ξ_K` and `σ = rationalHeight ρ`, a finite set `I` of simple roots
with root set `J = rootSet i ν I`, a Haar measure `ν_U` on `U_J(F)`, and `x, y ∈ G(F)`.

1. `exists_constantTermPremises_of_joint hJoint` (module
   `RationalSpecialCompactConstantTermPremises`) gives one compact open `K0` with
   `G(F) = P₀(F) K0`, `SimultaneousStandardBasisAt i ν K0`, `FiniteCartanCovering F i ν K0`, and,
   for `J ⊆ Δ` (`rootSet_subset`), `StandardLeviCartanCovering F i ν J K0` and
   `M_J(F) = (P₀(F) ∩ M_J(F))(K0 ∩ M_J(F))`.
2. `RationalConstantTermEstimateStatement.integrable_mul_mul h` (module
   `RationalCuspidalConvergenceReductions`), applied with this `K0` both as the subgroup of the
   structural premises and as the subgroup `K'` of the Iwasawa factorizations, and with the given
   `K`, gives the integrability of `v ↦ f(x v y)` on `U_J(F)`. That theorem passes from `Ξ_K` to
   `Ξ_{K0}` by the comparison `rationalSchwartzSubmodule_eq` (module `XiCompactComparison`). It then
   applies the estimate of Proposition II.4.5 at `m = 1` to the translate of `f`. The membership of
   `f` in the Schwartz submodule is `Space.coe_mem f`.

The hypothesis that `J` is proper is not used. The integrability holds for every `J ⊆ Δ`.

### `RationalConstantTermEstimateStatement.cuspidalVanishingComparison`

`(h : RationalConstantTermEstimateStatement.{u}) (hJoint : JointSpecialCompactBasisExistenceStatement.{u}) :
RationalCuspidalVanishingComparisonStatement.{u}`.

Proof. It is the published `RationalSchwartzConstantTermConvergenceStatement.vanishingComparison`
applied to the previous theorem.

## Remarks for the executors of Tasks 5480 and 5460

These remarks explain the choice of hypotheses. Remark 2 is a mathematical explanation and is
not formalized.

1. **Target 1 uses only clause 2 of `RationalSplitCenterHeightStatement`.** The reduction
   `RationalSplitCenterHeightStatement.schwartzCentralConvergence` goes through the published
   `RationalSplitCenterHeightStatement.centralWeights`, whose proof uses only the second clause
   (for every Haar measure `μ_A` on `A_G(F)` there is `r₀` with
   `∫⁻ (1 + σ(a))^{-r₀} dμ_A(a) < ∞`). The first clause (`1 + σ(a) ≤ C (1 + σ(a g))` on `G¹`) is
   not used for target 1.
2. **Target 2 needs the decay of Waldspurger's Lemmas II.4.2 and II.4.4.** A Schwartz function
   only satisfies `|f(g)| ≤ c Ξ(g) (1 + σ(g))^{-r}`. Bounding `Ξ` by a constant leaves the weight
   `(1 + σ(u))^{-r}` on `U_J(F)`, and this weight is not integrable on a nontrivial unipotent
   radical for any `r`. For example, in `SL₂` with its standard representation and `u = n(x)`, one
   has `σ(n(x)) = k log q` when `|x|_F = q^k`, `k ≥ 0`. The Haar measure of `{|x|_F = q^k}` is
   proportional to `q^k`, so `∫ (1 + σ)^{-r}` is a multiple of `Σ_k q^k (1 + k log q)^{-r} = ∞`.
   The Haar volume of `{σ ≤ R}` grows exponentially in `R`. The Library's integrability results
   on unipotent subgroups (module `UnipotentHeightIntegrability`) concern negative powers of the
   matrix norm `e^{σ}`, not of `1 + σ`. The missing decay is the factor
   `δ₀(m₀(ū))^{1/2}` of Lemma II.4.4 (`Ξ(mū) ≤ c δ₀(m)^{1/2} δ₀(m₀(ū))^{1/2} (1 + σ(mū))^d`),
   made integrable by Lemma II.4.2 (`∫_Ū δ₀(m₀(ū))^{1/2} (1 + σ(ū))^{-d} dū < ∞` for some `d`).
   Hence target 2 is reduced to Proposition II.4.5, whose proof uses both lemmas, and not to a
   cruder estimate.

## Provenance

Internal. The only new declaration that is not a theorem is the proposition
`RationalConstantTermConvergenceReductionStatement`, an implication between propositions already
published in the Library, and the module proves it. The source correspondence of the
hypotheses and targets is in the Markdown of their modules. The citations of Remark 2 are to
J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333 (literature id `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`): Lemma II.4.2, printed p. 261
(PDF p. 27); Lemma II.4.4 and Proposition II.4.5, printed p. 262 (PDF p. 28).

## Dependencies

The imported modules `RationalCuspidalConvergenceReductions` and `XiCompactComparison` are
published in the Library (Worker 824). The helper module
`RationalSpecialCompactConstantTermPremises` is part of this contribution.
