# Twisting by small characters at an arbitrary deep linearization

Author: Worker 1838. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. It is a
single-field companion of the published `rankOneStability`. That theorem uses one
linearizing element of its own choice. This unit accepts any element `c` that
linearizes the character on some deep lattice, provided `c` is large enough. That is
the form needed when the linearizing element comes from a smaller field
(`BrauerKernel.RamifiedTwist`).

Everything is in `Langlands.LocalFactor.RankOneStability`, for an arbitrary finite
p-adic field `F` with arbitrary supplied topological data `T`. The character `χ` is a
quasicharacter of `F^×`, `ψ` a nontrivial unitary additive character, and `c` a unit.
The deep-lattice hypothesis `hlin` says that for every `x` in the lattice
`T.additiveLattice (-m₀)` (that is, `ord x ≥ m₀`, with `m₀ > 0`),
`χ(1 + x) = ψ(c x)`. Here `1 + x` is the published `oneAddUnit`.

## Statements

- `lt_multiplicativeConductor_of_linearization`: under `hlin`, if `m₀ ≤ j` and
  `ord c + j < -n(ψ)`, then `j < a(χ)`.
- `abelianEpsilonExpression_mul_of_linearization`: assume `hlin`, `0 < K`,
  `ord c + (m₀ + K) ≤ -n(ψ)` and `ord c + 2K ≤ -n(ψ)`. Then for every quasicharacter
  `η` with `a(η) ≤ K` and every regular additive Haar measure `μ`,
  `T.abelianEpsilonExpression (χ * η) ψ μ = η(c⁻¹) · T.abelianEpsilonExpression χ ψ μ`.

## Proofs

The conductor bound: pick `w` in the lattice of level `n(ψ) + 1` with `ψ(w) ≠ 1`
(the published `exists_nontrivial_at_conductor_succ`). The element `x = c⁻¹ w` has
order at least `j`, so `1 + x ∈ U^j`, and `χ(1 + x) = ψ(w) ≠ 1`. Hence `χ` is not
trivial at level `j`, and `j < a(χ)` by `multiplicativeTrivialAt_iff_conductor_le`.

The twist identity: applying the bound at `j = max(m₀ + K, 2K) - 1` gives
`a = a(χ) ≥ m₀ + K` and `a ≥ 2K`. Put `m = a - K`. Then `m₀ ≤ m`, `K ≤ m`,
`m < a ≤ 2m` and `a = m + K`, and `hlin` restricts to the lattice of level `m`. As in
the published `exists_deep_linearization`, the order of `c` is exactly
`-(n(ψ) + a)`:
- `χ` is trivial on `U^a`, so `ψ(c x) = 1` on the lattice of level `a`. By
  `mem_additiveLattice_of_forall_complex_mul_eq_one` this gives `ord c ≥ -(n(ψ) + a)`.
- Some `v ∈ U^(a-1)` has `χ(v) ≠ 1` (`exists_nontrivial_below_multiplicativeConductor`).
  Then `ψ(c (v - 1)) ≠ 1`, so by `complex_eq_one_of_mem_conductor` we get
  `ord c < -(n(ψ) + a - 1)`.

The published stationary-phase identity `gauss_integral_twist`, with levels
`(a, m, K)`, now gives the Gauss-integral identity with factor `η(c⁻¹)`. The published
`conductor_and_L` (`2 a(η) ≤ a`) gives `a(χη) = a`. So both epsilon expressions are
ramified Gauss integrals on the same shell. Via
`deligneConstant_eq_abelianEpsilonExpression` and the definitions of
`deligneConstant`, `epsilon` and `epsilonAt`, they are exactly the two sides of that
identity.

## Provenance

Deligne, *Les constantes des équations fonctionnelles des fonctions L* (1973),
registered as `deligne-1973-local-constants`, SHA256
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`, proof of
Lemma 4.16, formula (4.16.1) (printed pages 545–546, PDF pages 45–46):
`ε(χα, ψ, dx) = χ(γ)^{-1} ε(α, ψ, dx)` for `χ` of small conductor, where `γ`
linearizes `α`. The hypotheses here are an internal reformulation: they replace
Deligne's exact conductor levels by lower bounds that hold for every sufficiently large
linearizing element. The proof reuses the published rank-one stability machinery named
above.
