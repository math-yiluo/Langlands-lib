# Continuous additive characters of `𝔸 / F` are unitary

Module `Langlands.Global.SmoothWhittakerExpansion.Character`, namespace
`Langlands.Global.SmoothWhittakerExpansion`. This helper module belongs to the proof of
`Langlands.Global.WhittakerExpansionStatement`. The statement assumes that `ψ : 𝔸 → ℂ` is a
continuous additive character, trivial on `F` and nontrivial. The Library's Whittaker
expansion core asks instead for `IsStandardAdditiveCharacter F ψ`, which consists of
continuity, nontriviality, triviality on `F` and `‖ψ x‖ = 1` for all `x`. This module proves
the missing unitarity.

## Results

* `exists_norm_le_of_trivial F ψ hc hF`: a continuous additive character `ψ` of the adeles,
  trivial on `F`, has bounded range. Proof: `ψ` is constant on cosets of the principal adeles,
  so it descends to a continuous function on the quotient `AdeleQuotient F = 𝔸 / F`. That
  quotient is compact (`compactSpace_adeleQuotient`), so the range is bounded.
* `norm_eq_one_of_trivial F ψ hc hF x`: `‖ψ x‖ = 1`. Proof: suppose `‖ψ y‖ > 1`. Then the
  values `‖ψ (k • y)‖ = ‖ψ y‖^k` are unbounded, a contradiction. So `‖ψ y‖ ≤ 1` for every
  `y`. Since `ψ (-x) ψ x = ψ 0 = 1`, the two norms multiply to `1`. Both are at most `1`, so
  both equal `1`.
* `isStandardAdditiveCharacter_of_continuous F ψ hc hF hne`: the hypotheses of
  `WhittakerExpansionStatement` on `ψ` give `IsStandardAdditiveCharacter F ψ`.

This is the standard fact that a continuous character of a compact group is unitary, applied
to the compact group `𝔸 / F`.
