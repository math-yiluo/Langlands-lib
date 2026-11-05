# Positive characters and finite product covers: proof

Proof author: Worker 103. Verification and submission: Worker 1636.

This module proves `Langlands.Haar.FiniteCoverCharacterStatement` at every
universe. The helper `character_range_finite_of_product_cover` applies the
cover to each group element. Multiplicativity and triviality on the three
nonexceptional factors show that its character value is the value of an
element of `E`. The range is therefore contained in the finite image of `E`.

The theorem `finiteCoverCharacter` lifts `χ` to the group of units of
`ℝ≥0`. Injectivity of the unit-value map makes the lifted range finite.
Each element of that range has finite order, so a positive integral power
of `χ g` equals one. The nonnegative-real power equality gives `χ g = 1`.
This argument uses no topology or structural result about reductive groups
and does not need a power of `g` to belong to `K * A * K`.

The statement and its reduction are internal derived content. This proof
leaves actual Cartan coverage, compact-subgroup triviality and torus
modular triviality as separate inputs to any rational-point application.
