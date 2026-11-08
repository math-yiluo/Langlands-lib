# Monomial gamma factors of highly ramified twists

Module `Langlands.Representation.RankinSelberg.HighlyRamified.MonomialGamma`.

This module supports the proof of
`Langlands.RankinSelberg.HighlyRamifiedGammaStabilityStatement`. It proves the
monomial gamma input of the adjacent-rank step,
`MonomialTwistGamma R`. It assumes `UniformRankOneTwistStatement` and level-uniform
stability of the adjacent pair `(R + 2, R + 1)` (`UniformPairStability (R + 1) R`).
Both are hypotheses and are not proved here.

## Provenance

Jacquet and Shalika 1985, §4.2 (printed pages 326–327). They apply
Proposition (4.1) to `π` and to the generic constituent of a principal series
`Ind(χ_1, …, χ_r)` with `∏ χ_i = ω_π`. By multiplicativity (Theorem (3.1) of
Jacquet, Piatetski-Shapiro and Shalika), the gamma factor of `(π ⊗ χ) × σ` becomes
a product of rank-one gamma factors once `a` is large. With the case `t = 1` they
conclude that `γ(s, (π ⊗ χ) × σ, ψ) = C_0 X^(r t a)`, where `C_0` depends only on
`χ`, `ω_π` and `ω_σ`. In (4.4.15) (printed page 329) they use this for
representations of ranks `r - 1` and `r - 2`. The interface `MonomialTwistGamma`
was agreed with Worker 1721, who uses it in the §4.4 argument.

The Lean proof differs from the source in four places. It also keeps every bound
uniform in the levels.
- Each rank-one factor `γ((τ ⊗ μ_i χ) × 1)` is evaluated directly by
  `UniformRankOneTwistStatement`, through `HighlyRamified.RankOneMonomial`. The
  test `τ` is not replaced by a principal series.
- The source takes the generic constituent of a principal series. The Lean proof
  instead builds the principal series by iterated pair induction
  `ρ × μ_(z_1) × ⋯ × μ_(z_(R+1))`. Each `z_i` avoids a finite set, so that every
  step is generic (`pairInductionGenericity`).
- The central character is matched by a final twist with an unramified character
  `μ_y`, where `y^(R+2) = w⁻¹`.
- The uniform comparison needs a level bound for the principal series, which the
  source does not discuss. It is given by `HighlyRamified.InducedLevel`.

## Definitions

All definitions use the canonical topological data of `F`, a character `ψ` of
conductor exponent `0`, and a self-dual `ν`.

- `MonomialTwistGamma R`: for all levels `m'` and `f` there is `A` with the
  following property. Let `σ` be generic of rank `R + 2` on a space in universe
  `uV`, with `HasPrincipalLevelVector F σ m'`, and let `χ` have `a(χ) ≥ A`. Then
  there is `C : (Fˣ →* ℂˣ) → ℂˣ` such that, for every generic `τ` of rank `R + 1`
  (space in `uV`) with a level-`f` vector and central character `ω`, every gamma
  factor of `(σ ⊗ χ ∘ det, τ)` is
  `rationalEpsilonMonomial (C ω) ((R + 2)(R + 1) a(χ))`.
- `RankOneMonomialBound F ψ ν R f B`: every gamma factor of
  `(τ ⊗ η ∘ det, 1)` is `c X^((R+1) a(η))` when `a(η) ≥ B`, for generic `τ` of rank
  `R + 1` and level `f`.
- `RankOneCommonBound F ψ ν R f B`: two such `τ` with the same central character
  have a common gamma factor of `(τ ⊗ η ∘ det, 1)` when `a(η) ≥ B`. This is the
  shape of the second part of `UniformRankOneTwistStatement`.
- `TwistGammaMonomial F ψ ν R f B I`, for `I` of rank `k + 1`: for every `χ` with
  `a(χ) ≥ B`, every gamma factor of `(I ⊗ χ ∘ det, τ)` is
  `c X^((k+1)(R+1) a(χ))`. Two such `τ` with the same central character give the
  same gamma factor. This is the induction predicate.

## Lemmas

- `multiplicativeConductor_mul_of_lt F χ ρ h`: if `a(ρ) < a(χ)`, then
  `a(ρ χ) = a(χ)`. The lower bound is `le_multiplicativeConductor_mul`. The upper
  bound holds because `ρ` and `χ` are both trivial on the units of level `a(χ)`.
- `rankOneExtensionCharacterTwistEquiv F ρ χ`: `ULift.moduleEquiv` is an
  equivalence from `(ρ ∘ det) ⊗ χ ∘ det` to `rankOneCharacter (ρ χ)`.
- `twistGammaMonomial_rankOneExtensionCharacter`: the base case. If
  `a(ρ) < B`, then `rankOneExtensionCharacter F ρ` satisfies
  `TwistGammaMonomial` with `k = 0`. A gamma factor of
  `((ρ ∘ det) ⊗ χ ∘ det, τ)` is one of `(τ ⊗ (ρ χ) ∘ det, 1)`. This uses the
  equivalence, `isPadicSymmetricGammaFactor_rankOne_test_twist` and
  `Padic.isPadicSymmetricGammaFactor_comm`. Since `a(ρ χ) = a(χ) ≥ B`, the two
  bound hypotheses apply.
- `rationalEpsilonMonomial_mul_coe`: `c X^m · c' X^(m') = (c c') X^(m + m')`.
- `exists_gammaFactor_twist_pairInduced`: for generic `A`, `C` with `A × C`
  generic, the gamma factor of `((A × C) ⊗ χ ∘ det, τ)` is the product of those of
  `τ` against `A ⊗ χ ∘ det` and `C ⊗ χ ∘ det`. The twist of the induction is the
  induction of the twists (`normalizedProductDeterminantTwistEquiv`). Then
  `gammaMultiplicativity` applies with two blocks.
- `twistGammaMonomial_pairInduced`: the induction step. If `A` (rank `k + 1`) and
  `C` (rank one) satisfy `TwistGammaMonomial` and `A × C` is generic, then
  `A × C` satisfies it with `k + 1`. The exponents add:
  `(k+1)(R+1)a + (R+1)a = (k+2)(R+1)a`.
- `twistGammaMonomial_twist_unramified`: `TwistGammaMonomial` passes to
  `I ⊗ μ_y ∘ det`. The twists combine (`twist_twist`), and
  `a(χ μ_y) = a(χ)` (`multiplicativeConductor_mul_unramified`).
- `isGeneric_rankOneExtensionCharacter`,
  `hasGLCentralCharacter_rankOneExtensionCharacter`, `unramifiedCharacter_mul`:
  the character `ρ ∘ det` of `GL_1` is generic with central character `ρ`, and
  `μ_(w z) = μ_w μ_z`.
- `exists_iteratedPrincipalSeries`: if `a(ρ) < B` and `a(ρ) ≤ m'`, then for every
  `n` there are a representation `I` of rank `n + 1` and `w : ℂˣ` with the
  following properties. `I` is generic, has a level-`m'` vector, has central
  character `ρ μ_w`, and satisfies `TwistGammaMonomial`. The proof is by
  induction on `n`. It starts from `ρ ∘ det` and passes from `I` to `I × μ_z` with
  `z` outside the finite set of `pairInductionGenericity`. The level comes from
  `hasPrincipalLevelVector_normalizedProductInduced`, the central character from
  `hasScalarCharacter_normalizedProductInduced`, and `TwistGammaMonomial` from the
  step lemma and the base case for `μ_z`.
- `exists_principalSeries`: under the same hypotheses on `ω`, there is a generic
  `σ'` of rank `R + 2` with a level-`m'` vector, central character exactly `ω`,
  and `TwistGammaMonomial`. It is the iterated principal series with `n = R + 1`,
  twisted by `μ_y ∘ det` with `y^(R+2) = w⁻¹` (`IsAlgClosed.exists_pow_nat_eq`).
  The twist multiplies the central character by `μ_y^(R+2) = μ_w⁻¹`
  (`hasGLCentralCharacter_twist`).

## Main theorem

- `monomialTwistGamma (h3 : UniformRankOneTwistStatement.{uF, max uF uV})
  (hIH : UniformPairStability.{uF, max uF uV, max uF uV} (R + 1) R) :
  MonomialTwistGamma.{uF, max uF uV} R`. Proof. Fix the levels `m'` and `f`.
  - `exists_bound_rankOne_gammaMonomial` (`HighlyRamified.RankOneMonomial`) and
    the second part of `h3` give bounds `B₁, B₂` at rank `R + 1` and level `f`.
    Set `B = max (max B₁ B₂) (m' + 1)`. Let `A₀` be the bound of `hIH` at the
    levels `(m', f)`, and take `A = max A₀ B`.
  - Given `σ` and `χ`, let `ω` be the central character of `σ`
    (`exists_quasicharacter_hasGLCentralCharacter`). Then `a(ω) ≤ m' < B`
    (`multiplicativeConductor_le_of_hasGLCentralCharacter`).
    `exists_principalSeries` gives `σ'` with central character `ω` and level `m'`.
  - For a central character `ω'`, suppose no admissible `τ` has central
    character `ω'`. Then any constant works. Otherwise fix such a `τ₀`, and let
    `c` be the constant of the monomial gamma factor of `(σ' ⊗ χ ∘ det, τ₀)`.
    Such a gamma factor exists, as `genericSymmetricGammaFactor_isPadic` shows.
    Let `τ` have central character `ω'`, and let `G` be a gamma factor of
    `(σ ⊗ χ ∘ det, τ)`. By `hIH`, applied to the candidates `σ, σ'` and the test
    `τ`, `G` is the gamma factor of `(σ' ⊗ χ ∘ det, τ)`. By the second part of
    `TwistGammaMonomial` for `σ'`, that gamma factor equals the one for `τ₀`.
    So `G = c X^((R+2)(R+1) a(χ))`. Choosing `c` for each `ω'` gives `C`.
