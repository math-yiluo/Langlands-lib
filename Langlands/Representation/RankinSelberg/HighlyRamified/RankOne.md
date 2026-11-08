# The rank-one case of gamma stability

Module `Langlands.Representation.RankinSelberg.HighlyRamified.RankOne`.

This module supports the proof of
`Langlands.RankinSelberg.HighlyRamifiedGammaStabilityStatement`. It derives
`PairStability r 0` and its level-uniform form `UniformPairStability r 0`, gamma
stability of `(π_i ⊗ χ ∘ det, σ)` for generic tests `σ` of `GL_1(F)`, from the
published statement
`Langlands.RankinSelberg.UniformRankOneTwistStatement`. That statement is only a
hypothesis here. This module does not prove it.

## Provenance

`UniformRankOneTwistStatement` is the level-uniform form of Jacquet and Shalika
1985, Proposition (2.2) (printed page 320), against the trivial character of
`GL_1`. Jacquet and Shalika use the rank-one case in §4.3 (printed page 327) for
tests of rank one. The reduction from an arbitrary character `η` of `GL_1` to the
trivial one is the identity
`γ(s, (π ⊗ χ ∘ det) × η, ψ) = γ(s, (π ⊗ (η χ) ∘ det) × 1, ψ)` together with the
conductor bound below. The source uses both facts without stating them as
lemmas. Their formal derivation here is internal to this project.

## Lemmas

All statements use the canonical topological data `F.canonicalTopologicalData`
of the p-adic field `F`.

- `le_multiplicativeConductor_mul F χ η h`: if `a(η) < a(χ)`, then
  `a(χ) ≤ a(η χ)`, where `a` is `multiplicativeConductor`. Proof: if
  `a(η χ) < a(χ)`, then both `η χ` and `η` are trivial on the units of level
  `a(χ) - 1`, by `multiplicativeTrivialAt_iff_conductor_le`. So `χ` is trivial on
  them too, and the same lemma gives `a(χ) ≤ a(χ) - 1`. This is impossible,
  because `a(χ) > a(η) ≥ 0`.
- `isPadicSymmetricGammaFactor_trivial_of_rankOne_test`: let `π` be generic of
  rank `r + 1`, and let `σ` be equivalent to `rankOneCharacter η`. Then every
  gamma factor `G` of `(π ⊗ χ ∘ det, σ)` is a gamma factor of
  `(π ⊗ (η χ) ∘ det, rankOneCharacter 1)`. The proof first replaces `σ` by
  `rankOneCharacter η` (`IsPadicSymmetricGammaFactor.congr_equiv`). It then
  exchanges the two arguments (`Padic.isPadicSymmetricGammaFactor_comm`; both
  sides are of Whittaker type by `isOfWhittakerType_of_isGeneric`,
  `isGeneric_quasicharacter_twist` and `rankOneCharacter_isOfWhittakerType`). It
  moves `η` from the test to a determinant twist
  (`isPadicSymmetricGammaFactor_rankOne_test_twist`), combines the two twists
  (`twist_twist`; `(η ∘ det) (χ ∘ det) = (η χ) ∘ det` holds by definition), and
  exchanges the arguments back.
- `scalar_mem_principalLevelSubgroup F n a u hu`: if `u` is a principal unit of
  level `a` (`u ∈ principalUnits a`: `|u| = 1` and `|u - 1| ≤ q^(-a)`), then the
  scalar matrix `u · 1` of `GL_(n+1)(F)` lies in
  `Conductor.principalLevelSubgroup F n a`, the image of the kernel of reduction
  modulo `𝔪^a` on `GL_(n+1)(O)`. The integral lift is the scalar matrix of the
  integral unit `u`. The entry condition `u - 1 ∈ 𝔪^a` comes from the Library
  identification `RankOneBox.levelSet_eq_additiveLattice` of `𝔪^a` with the
  valuation lattice of level `-a`.
- `multiplicativeConductor_le_of_hasPrincipalLevelVector F σ η e h`: if `σ` is
  equivalent to `rankOneCharacter η` and has a nonzero vector `v` fixed by
  `principalLevelSubgroup F 0 m`, then `a(η) ≤ m`. For `u ∈ principalUnits m`
  the scalar matrix `u` fixes `v`, so `η(u)` fixes the nonzero vector `e v`, and
  `η(u) = 1`. So `η` is trivial on `principalUnits m`, and
  `multiplicativeTrivialAt_iff_conductor_le` gives the bound.

## Main theorems

- `pairStability_rankOne (h : UniformRankOneTwistStatement.{uF, uV}) r :
  PairStability.{uF, uV, uW} r 0`. Proof. Let `π₁, π₂` be generic of rank `r + 1`
  with the same central character, and `σ` generic of rank one.
  `rankOneCharacterReduction` writes `σ` as `rankOneCharacter η`.
  `HighlyRamified.exists_hasPrincipalLevelVector` gives levels `m₁, m₂` with
  `HasPrincipalLevelVector F π_i m_i`. By `HasPrincipalLevelVector.mono` both
  hold at `max m₁ m₂`. Let `B` be the bound of `UniformRankOneTwistStatement` at
  rank `r + 1` and level `max m₁ m₂`, and set `A = max B (a(η) + 1)`. For
  `a(χ) ≥ A`, `le_multiplicativeConductor_mul` gives `a(η χ) ≥ a(χ) ≥ B`. The
  second part of the statement then gives a common gamma factor `G` of
  `(π_i ⊗ (η χ) ∘ det, 1)` for `i = 1, 2`. By
  `isPadicSymmetricGammaFactor_trivial_of_rankOne_test` and uniqueness of gamma
  factors (`IsPadicSymmetricGammaFactor.unique`), any gamma factors `G₁, G₂` of
  `(π_i ⊗ χ ∘ det, σ)` both equal `G`.
- `uniformPairStability_rankOne (h : UniformRankOneTwistStatement.{uF, uV}) r :
  UniformPairStability.{uF, uV, uW} r 0`, the level-uniform form. Given levels
  `m` for the candidates and `m'` for the test, let `B` be the bound of the
  statement at rank `r + 1` and level `m`, and set `A = max B (m' + 1)`. The
  test is `rankOneCharacter η` with `a(η) ≤ m'`, by
  `multiplicativeConductor_le_of_hasPrincipalLevelVector`. So for `a(χ) ≥ A`
  the conductor bound gives `a(η χ) ≥ a(χ) ≥ B`, and the proof ends as for
  `pairStability_rankOne`. The bound `A` depends only on `r`, `m` and `m'`.
- `highlyRamifiedGammaStability_of_adjacent_and_uniformRankOne`: the target
  statement `HighlyRamifiedGammaStabilityStatement.{uF, uV, uW}` follows from
  the adjacent case `∀ n, PairStability (n + 1) n` at the universe pairs
  `(uV, uW)`, `(max uF uV, uW)` and `(uV, max uF uW)`, and
  `UniformRankOneTwistStatement.{uF, uV}`. It applies
  `highlyRamifiedGammaStability_of_adjacent_and_rankOne`
  (`HighlyRamified.PairInductionGenericity`), with both rank-one inputs given by
  `pairStability_rankOne`.

- `highlyRamifiedGammaStability_of_uniformAdjacent_and_uniformRankOne`: the
  target statement `HighlyRamifiedGammaStabilityStatement.{uF, uV, uW}` follows
  from the uniform adjacent case
  `∀ n, UniformPairStability.{uF, U, U} (n + 1) n` with `U = max uF uV uW`, and
  `UniformRankOneTwistStatement.{uF, uV}`.
  `pairStability_of_uniformPairStability` turns the uniform case into
  `PairStability.{uF, U, U} (n + 1) n`. `pairStability_of_common`
  (`HighlyRamified.UniverseTransport`) moves it to the three universe pairs
  above, because `max uF (max uF uV) uW` and `max uF uV (max uF uW)` are both
  `U`. Then `highlyRamifiedGammaStability_of_adjacent_and_uniformRankOne`
  applies.

So the remaining inputs of the target are the adjacent case, which is the
Jacquet and Shalika §4.4 argument, and a proof of
`UniformRankOneTwistStatement`.
