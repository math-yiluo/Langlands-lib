# Finiteness of Henniart's candidate sets from the conductor theorems

Author: Worker 4803. Module `Langlands.Correspondence.HenniartConductorFinitenessProof`,
namespace `Langlands.Henniart.Extension`. Universes: `uK` (p-adic fields) and `uV`
(supercuspidal carriers), independent.

## Statement: `SupercuspidalEpsilonConductorFinitenessReductionStatement.{uK, uV}`

The implication below, proved as `supercuspidalEpsilonConductorFinitenessReduction`
from the theorem `supercuspidalEpsilonConductorFiniteness_of_conductor`:

`Henniart.SupercuspidalBoundedLevelFinitenessStatement.{uK, uV} →
RankinSelberg.PairEpsilonExponentStatement.{uK, uV, 0} →
Conductor.ConductorExponentStatement.{uK, uV} →
SupercuspidalEpsilonConductorFinitenessStatement.{uK, uV}`.

The conclusion is the published component of `HenniartStableMapStatement`: for a
nontrivial additive character `ψ` of a p-adic field `K`, a measure `ν` self-dual
for `ψ`, a rank `k + 1`, a character `ω` of `Kˣ` and an integer `m`, only finitely
many supercuspidal classes `π` of `GL_(k+1)(K)` have central character `ω` and an
epsilon factor `c q^(-ms)` against the trivial character of `GL_1(K)`.

The three hypotheses are published Library statements, and the theorem asserts
none of them:

- `SupercuspidalBoundedLevelFinitenessStatement` (Bernstein–Zelevinsky 1976,
  Corollary 4.15): for a fixed central character and a bound `b`, finitely many
  supercuspidal classes have a nonzero vector fixed by the level-`b` subgroup.
- `PairEpsilonExponentStatement` (Bushnell–Henniart–Kutzko 1998): for an
  irreducible admissible pair there is an integer `a` such that every epsilon
  factor `c q^(-ms)` of the pair, for every `ψ` and every measure self-dual for
  `ψ`, has `m = a + (r+1)(t+1) n(ψ)`. Here `n(ψ)` is the additive conductor
  exponent. It is used with the trivial character of `GL_1` on `ℂ`, so its third
  universe is `0`.
- `ConductorExponentStatement` (Jacquet, Piatetski-Shapiro and Shalika 1981,
  Théorème (5.1)): for `ψ` of conductor `𝔒` and a generic `π`, the exponent of the
  epsilon factor of `π` against the trivial character of `GL_1` is the least level
  with nonzero fixed vectors.

## Supporting results

- `trivialRankOneEquiv`: the constructed representative
  `rankOneSupercuspidalObject K 1` of the trivial rank-one class, on `ULift ℂ`, is
  equivalent to the scalar model `RankinSelberg.rankOneCharacter 1` on `ℂ`.
- `exists_newvectorConductor_of_pairEpsilon`: assume the second and third
  hypotheses. Let `A` represent a supercuspidal class of `GL_(k+1)(K)`, and let
  `c q^(-ms)` be its epsilon factor against the trivial character of `GL_1`, for
  `ψ` and `ν` self-dual for `ψ`. Then `m - (k+1) n(ψ)` is a natural number `b`, and
  `A` has newvector conductor `b`.

## Provenance

Internal. Henniart (2000), §4.3, printed p. 452 (PDF p. 14): the central character
of `π(σ)` is fixed, and its conductor is fixed by `ε(σ, s, ψ) = ε(π, s, ψ)`, "il
n'y a donc qu'un ensemble fini `P` de possibilités". Henniart gives no further
argument. The Lean proof uses the three published statements above with these
sources: Bernstein and Zelevinsky (1976), Corollary 4.15, printed p. 41; Bushnell,
Henniart and Kutzko (1998), introduction, printed p. 703; Jacquet,
Piatetski-Shapiro and Shalika (1981), Théorème (5.1), printed p. 211.

## Proof

- `exists_newvectorConductor_of_pairEpsilon`. Transport the epsilon factor along
  `trivialRankOneEquiv` and read it as an epsilon factor of `A` against
  `rankOneCharacter 1` (`isPadicSymmetricEpsilonFactor_of_le`). `A` is generic
  for every additive character by the published Gelfand–Kazhdan theorem
  `isGeneric_of_isSupercuspidal`. Take `a` with `ψ_a(x) = ψ(ax)` of conductor `𝔒`
  (`exists_scale_hasIntegerConductor`). The published `genericConductor_eq` gives
  `f_ψ(A) = m - (k+1) n(ψ)` for the constructed conductor `f_ψ`. The second
  hypothesis gives `f_ψ(A) = f_(ψ_a)(A)`
  (`genericPairConductor_eq_of_pairEpsilonExponentStatement`). The third gives a
  natural number `b` with `f_(ψ_a)(A) = b` and newvector conductor `b`
  (`genericConductor_isNewvectorConductor_of_conductorExponentStatement`).
- `supercuspidalEpsilonConductorFiniteness_of_conductor`. The scalar matrices
  give an isomorphism `e : Kˣ ≃* Z(GL_(k+1)(K))`. Put `χ = ω ∘ e⁻¹` and
  `b = (m - (k+1) n(ψ)).toNat`. The set is contained in the bounded-level stratum
  `SupercuspidalClass.centralLevelStratum χ b`, which is finite by the first
  hypothesis. For a member `π` with representative `A`:
  - `A` has central character `χ` by `supercuspidalCentralActsBy_iff`;
  - `A` has newvector conductor `b` by the previous lemma, so its level-`b` fixed
    space is nonzero, and `firstFixedLevel_le_iff` gives
    `firstFixedLevel π ≤ b`.

Standard axioms only.
