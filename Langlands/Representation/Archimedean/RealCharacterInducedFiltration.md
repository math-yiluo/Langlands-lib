# The filtration for a character followed by an induction block on `GL₃(ℝ)`

Lean module: `Langlands.Representation.Archimedean.RealCharacterInducedFiltration`, namespace
`Langlands.Archimedean.RealCharacterInducedFiltration`.

## Role and provenance

This module assembles the proof of `Langlands.Archimedean.RealCharacterInducedFiltrationStatement`
(Library module `RealInducedPairFiltrationReduction`, Task 7133) from its cases. The cases are
proved in `RealCharacterInducedWeightZero`, `RealCharacterInducedPushforward` and
`RealCharacterInducedSwap`. The main theorem assumes two statements that are not proved here:

- `RealSwapLandingStatement` (module `RealSwapLandingStatement`);
- `RealOrthogonalBlockUncertaintyStatement` (module
  `RealOrthogonalUncertaintyStatement`).

The filtration for two characters is used through Task 7067's theorem
`realCharacterPairFiltration` (module `RealCharacterPairFiltration`). The case split is
specific to this project, and no literature statement is formalized, so the module has no
sources.

## Notation

`c = sgn^ε |·|^s` (`c.parity = ε`, `c.exponent = s`). `d` has weight `m` and exponent `t`,
`ℓ = |m|` (`d.weight.natAbs`), `b = t - ℓ/2`, and `w = b - s`. The hypothesis of the target
statement is `Re s < Re t` (`realBlockExponent` of a block is the real part of its exponent).

## Declarations

- `lt_of_neg`: if `ℓ > 0`, `Re s < Re t` and `w = -m₀` for a natural number `m₀`, then `m₀ < ℓ`.
  Proof: taking real parts, `-m₀ = Re t - ℓ/2 - Re s > -ℓ/2`, so `m₀ < ℓ/2 < ℓ`.
- `realCharacterInducedFiltration_of`: `RealSwapLandingStatement` and
  `RealOrthogonalBlockUncertaintyStatement` imply `RealCharacterInducedFiltrationStatement`.

  Proof. Let `c`, `d` with `Re s < Re t`.
  - `ℓ = 0`: `RealStandardFiltration.realAdjacentFiltration_character_induced_of_weight_eq_zero`
    with `realCharacterPairFiltration`.
  - `ℓ > 0` and `w = k` for an integer `k ≠ 0`:
    - `k = -m₀ < 0`: `m₀ < ℓ` by `lt_of_neg`. If `m₀ + ε` is even, apply
      `RealCharacterInducedSwap.filtration_tail_second` with the second half of the landing
      statement (`RealSwapLandingCharacterFirstStatement`). If it is odd, apply
      `RealCharacterInducedSwap.filtration_tail_first` with the first half
      (`RealSwapLandingInducedFirstStatement`). Both also use the uncertainty statement.
    - `k > 0`: apply `RealCharacterInducedPushforward.filtration_reducible` with the sign
      `s_b = (ε + k) mod 2`, so that `ε + s_b ≡ k (mod 2)`. Here `(chiB d s_b).exponent = b` by
      definition.
  - `ℓ > 0` and `w` not a nonzero integer: apply
    `RealCharacterInducedPushforward.filtration_generic` with the sign `s_b = (ε + 1) mod 2`, so
    that `ε + s_b` is odd.

  The pushforward cases use the second half of the landing statement.
