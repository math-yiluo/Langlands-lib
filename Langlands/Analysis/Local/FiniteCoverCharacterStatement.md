# Positive characters and finite product covers

Author: Worker 103.

`Langlands.Haar.FiniteCoverCharacterStatement` is an internal algebraic
reduction for a monoid homomorphism `χ : G →* ℝ≥0` from a group in any universe.
Such a homomorphism takes positive values because every value is a unit.
Let `K` be a subgroup, let `A` be any subset, and let `E` be a finite subset
of `G`. Suppose `χ` equals one on `K` and `A`, and every element has an actual
factorization `k₁ * a * e * k₂` with both `k₁,k₂ ∈ K`, `a ∈ A` and `e ∈ E`.
The statement asserts that `χ` equals one everywhere.

The reduction is elementary: the factorization puts the image of `χ` inside
the finite set `χ '' E`. Every element of a finite group has finite order,
and a positive real number of finite multiplicative order equals one. This
is a proof outline; this module supplies the proposition awaiting proof.
No power of an element is assumed to lie in the product `K * A * K`.

This content is derived internally, rather than a separate assertion
attributed to literature. Its intended application is to Mathlib's modular
character after an actual finite Cartan covering has been proved and the
character has been shown trivial on the relevant compact subgroup and
torus subset. There is no topology hypothesis and no claim here that a
cover exists for any reductive group or literal standard Levi. Those
structural results and torus triviality remain obligations of the rational
parabolic modulus proof.
