# The inductive step of Henniart's rank induction

Author: Worker 4803. Module `Langlands.Correspondence.HenniartChoiceIndependenceStepProof`,
namespace `Langlands.Henniart.Extension`. Universes: `uK` (p-adic fields), `uW`
(Weil carriers), `uV` (supercuspidal carriers), `uE` (local-constant values in
the candidate properties), all independent.

## Main results

- `stableExistsAt_succ_succ`. Fix `K : PadicField.{uK} p`, a geometric
  reciprocity candidate `e` of `K`, and a local-constant system
  `hε : NonabelianSystem.IsSystem K eC ε`. Assume:
  - `CandidateExistenceStatement.{uK, uW, uV, uE, uK}`;
  - `SupercuspidalEpsilonConductorFinitenessStatement.{uK, uV}`;
  - `RankinSelberg.UnramifiedTwistEpsilonStatement.{uK, uV, uV}`;
  - `RankStage.{uK, uW, uV, uE} K r` for every `r < k + 2`.

  Then `StableExistsAt.{uK, uW, uV, uE} K (k + 2)`, with `k + 2` written as
  `(k + 1).succPNat`. That is, every unitary irreducible Weil class of dimension
  `k + 2` that factors through a finite quotient has a stable image.
- `choiceIndependenceStep_of_inputs` proves

  `CandidateExistenceStatement.{uK, uW, uV, uE, uK} →
  SupercuspidalEpsilonConductorFinitenessStatement.{uK, uV} →
  LocalClassField.CommonClosureReciprocityExistence.{uK} →
  (∀ p K eC, NonabelianSystem.Exists.{uK, uE} K eC) →
  ChoiceIndependenceStepStatement.{uK, uW, uV, uE}`.

  It takes a normalized family `eC` from local reciprocity, the geometric
  candidate `baseReciprocityCandidate K eC` (`baseGeometricReciprocityProof`) and
  a local-constant system for `eC`. It writes `n > 1` as `(k + 1).succPNat` and
  uses the published `RankinSelberg.unramifiedTwistEpsilon`.

All hypotheses are published Library statements, and neither result asserts them.

## Supporting results

- `isSupercuspidalPairEpsilonFactor_unramifiedTwist_right`. Assume the
  unramified-twist law. If `(c, m)` is an epsilon certificate of the
  supercuspidal pair `(π, τ)`, then `(c z^m, m)` is one of `(π, τ')`. Here `τ'` is
  the twist of `τ` by `fieldUnramified K z`.
- `unitaryPairEpsilon_generator_unique`. For one local-constant system and one
  `ψ`, the Weil epsilon certificate of a pair of unitary generators is unique.
- `candidate_character_generator`. A map with `LatticeMap.HenniartProperties`
  sends the rank-one Weil class of a modulus-one character `χ`, which lies in its
  domain, to the generator of the `GL₁` class of `χ`.
- `candidate_centralCharacter`. If such a map sends the generator of `σ` to the
  generator of `π`, then `π` has a central character `ω` with
  `ω ∘ rec_e = det σ`.
- `candidate_pairEpsilon`. If such a map sends the generators of `a` and `b` to
  those of `π` and `τ`, then one certificate is both the Weil epsilon factor of
  `(a, b)` and the epsilon factor of the pair `(π, τ)`.
- `candidate_image_mem`. Fix `ω₀` with `ω₀ ∘ rec_e = det σ`, and let `c₀` be the
  Weil epsilon certificate of `σ` with the trivial rank-one class. Suppose such a
  map sends the generator of `σ` to that of a unitary class `π` of `GL_(k+2)`.
  Then `π` has central character `ω₀`, and the pair `(π, 1_GL₁)` has an epsilon
  certificate with exponent `c₀.2`.
- `agree_of_unitaryBasisPairEpsilon`. Let `π, π'` be unitary classes of
  `GL_(k+2)` with a common epsilon certificate against a unitary class `t₀`, and
  let the test `t` be the unramified twist of `t₀` by `z`. Then `π` and `π'` agree
  at `t` in the sense of `FiniteEpsilon.Agree`.
- `exists_lift_of_lowerRank`. Assume `RankStage K r` for every `r < k + 2`. Then
  every test `t : FiniteEpsilon.SupercuspidalTest K k` (a supercuspidal class of
  some rank `r + 1 ≤ k + 1`) is the unramified twist, by some `z`, of a unitary
  class `t₀`, and `t₀` is the stable image of some unitary Weil class `σ_t`.

## Provenance

Internal proof of the published `ChoiceIndependenceStepStatement` (module
`HenniartStableMapStatement`). It follows Henniart (2000), §4.3, proof of 4.2 a),
printed pp. 452–453 (PDF pp. 14–15). Fix `σ`. The central character of
`π(σ)` is fixed by `ω ∘ τ_F = det σ`, and its conductor by
`ε(σ, s, ψ) = ε(π, s, ψ)`, so only a finite set `P` of values is possible. Any
two members of `P` are separated by an epsilon factor against some `τ` of rank
`r < n` (Henniart's Théorème 1.4). An unramified twist of `τ` does not affect
this, so one may assume `ω_τ` has finite order. By induction `τ = π(σ')`, and
one takes `E(σ)` to be the compositum of the fixed field of `ker σ` and the
fields `E(σ')`.

The Lean proof follows the same route with these differences.

- The conductor condition is stated as the exponent `m` in the epsilon factor
  `c q^(-ms)` of the pair of `π` with the trivial character of `GL₁`. This is the
  form of `SupercuspidalEpsilonConductorFinitenessStatement`.
- Separation by a fixed finite family of tests is the published
  `finiteSupercuspidalEpsilonSeparation_of_localConverse` (module
  `SupercuspidalFiniteEpsilonProof`), applied to the published
  `RankinSelberg.supercuspidalLocalConverse`.
- The reduction to finite-order central characters uses
  `exists_unitaryFiniteOrderTwist` (module `HenniartUnitaryTwistProof`). Agreement
  at the twisted test then follows from agreement at the untwisted one by the
  unramified-twist law.
- The compositum of fields is replaced by a product of finite quotients of the
  absolute Galois group.

## Proof of `stableExistsAt_succ_succ`

1. Take a nontrivial additive character `ψ`
   (`HarmonicAnalysis.padicUnitaryAdditiveCharacterExists`) and a finite quotient
   `q₀` through which `σ` factors. Take a candidate `Φ₀` at `q₀` (candidate
   existence) and a self-dual measure `ν` for `ψ`, which the candidate's pair
   factor clause provides.
2. From `Φ₀`: a character `ω₀` with `ω₀ ∘ rec_e = det σ`
   (`candidate_centralCharacter`), and the Weil epsilon certificate `c₀` of `σ`
   with the trivial rank-one class (`candidate_character_generator`,
   `candidate_pairEpsilon`).
3. Let `P` be the set of classes of `GL_(k+2)` with central character `ω₀` and an
   epsilon certificate against `1_GL₁` with exponent `c₀.2`. `P` is finite by the
   conductor finiteness input. The separation theorem gives a finite family `D`
   of tests that separates `P`.
4. For every test, `exists_lift_of_lowerRank` gives `z`, `t₀` and `σ_t`, and
   `IsStableImage.exists_quotient` gives a finite quotient `q_t` for the stable
   image of `σ_t`. Index `D` by `Fin D.card` (`Finset.equivFin`), which keeps the
   product quotient in universe `uK`. Let `r = q₀ × ∏_i q_(t_i)`. Then `σ` factors
   through `r` (`unitaryFiniteFactoringSupported_comp_le` with the first
   projection).
5. Take a candidate `Φ_r` at `r`. Its value on `σ` is the claimed stable image.
   Let `Φ` be any candidate at `r`. By `IsCandidate.exists_generator`, `Φ σ` and
   `Φ_r σ` are generators of unitary classes `π`, `π'` of rank `k + 2`, and both
   lie in `P` (`candidate_image_mem`). For each test `t ∈ D`, `Φ` and `Φ_r` both
   send `σ_t` to `t₀`, because `r` maps onto `q_t` through a projection. The
   certificates of `(σ, σ_t)` given by the two candidates are equal
   (`candidate_pairEpsilon`, `unitaryPairEpsilon_generator_unique`). So `π` and
   `π'` have a common certificate against `t₀`, and agree at `t`
   (`agree_of_unitaryBasisPairEpsilon`). Separation gives `π = π'`, hence
   `Φ σ = Φ_r σ`.

Standard axioms only.
