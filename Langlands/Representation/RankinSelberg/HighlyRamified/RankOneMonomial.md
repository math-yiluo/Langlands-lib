# Gamma factors against the trivial character after a highly ramified twist

Module `Langlands.Representation.RankinSelberg.HighlyRamified.RankOneMonomial`.

This module supports the proof of
`Langlands.RankinSelberg.HighlyRamifiedGammaStabilityStatement`. It shows that the
gamma factor of `(τ ⊗ η ∘ det) × 1` is a monomial `c X^((n+1) a(η))` once `a(η)`
is large. The bound is uniform over generic `τ` of rank `n + 1` with a given
principal level. The argument assumes `UniformRankOneTwistStatement` and does not
prove it.

## Provenance

Jacquet and Shalika 1985, Proposition (2.2) (printed page 320), gives
`L(s, (τ ⊗ η) × 1) = 1` and `ε(s, (τ ⊗ η) × 1, ψ) = c q^(-(n+1) a s)` for `η` of
large conductor `a`. In the Library this is the first part of
`UniformRankOneTwistStatement`, with a bound that is uniform in the level. In
§4.2 (printed pages 326–327), Jacquet and Shalika use it to write the gamma
factor as a monomial. The gamma factor also involves the `L`-function of the
dual pair. Here it is handled by applying the same statement to the dual pair.
That step and its formal derivation are internal to this project.

## Lemmas

- `rationalGammaExpression_one_one δ c m`: with both `L`-polynomials equal to
  `1`, `rationalGammaExpression δ c m 1 1` is `rationalEpsilonMonomial c m`, the
  rational function `c X^m`.

## Main theorem

- `exists_bound_rankOne_gammaMonomial h F ψ ν hψ n f`. Assume
  `h : UniformRankOneTwistStatement.{uF, uV}`, a character `ψ` of conductor
  exponent `0`, and a self-dual `ν`. Then for every rank `n + 1` and level `f`
  there is `B` with the following property. Let `τ` be generic for `ψ`, of rank
  `n + 1` and on a space in universe `uV`, with
  `HasPrincipalLevelVector F τ f`, and let `η` be a quasicharacter with
  `a(η) ≥ B`. Then every gamma factor `G` of
  `(τ ⊗ η ∘ det, rankOneCharacter 1)` (`IsPadicSymmetricGammaFactor`) is
  `rationalEpsilonMonomial c ((n + 1) a(η))` for some `c : ℂˣ`.

  Proof. Let `B₁` be the bound of the statement for `(ψ, ν)` and `B₂` the bound
  for `(ψ.scale (-1), negatedSelfDualHaar F ψ ν)`. Here `ψ.scale (-1)` has
  conductor exponent `0` by `additiveConductor_scale_neg_one`. Take
  `B = max B₁ B₂`.
  - The first part of the statement for `τ` and `η` gives the `L`-polynomial `1`
    and the epsilon factor `(c, (n + 1) a(η))` of `(τ ⊗ η ∘ det, 1)`.
  - On the dual side, `inverseTransposePullback τ` is generic for `ψ.scale (-1)`
    and has a level-`f` vector (`HighlyRamified.Duality`), and
    `a(η⁻¹) = a(η) ≥ B₂`. So the first part of the statement for
    `(ψ.scale (-1), inverseTransposePullback τ, η⁻¹)` gives the `L`-polynomial
    `1` of `((inverseTransposePullback τ) ⊗ η⁻¹ ∘ det, 1)`. The equivalences
    `inverseTransposePullbackTwistEquiv` and
    `inverseTransposePullbackTrivialEquiv` identify this pair with
    `(inverseTransposePullback (τ ⊗ η ∘ det), inverseTransposePullback 1)`
    (`IsPadicSymmetricLPolynomial.congr_equiv`).
  - Both `τ ⊗ η ∘ det` and the trivial character are of Whittaker type
    (`isOfWhittakerType_of_isGeneric`, `isGeneric_quasicharacter_twist`,
    `rankOneCharacter_isOfWhittakerType`). So
    `whittakerTypeGammaConstructionInput` gives the construction input. Then
    `symmetricGammaExpression` gives
    `G = rationalGammaExpression δ c ((n + 1) a(η)) 1 1`, which is the monomial
    by `rationalGammaExpression_one_one`.
