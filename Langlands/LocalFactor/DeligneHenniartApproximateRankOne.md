# The approximate rank-one twist relation

This module proves Deligne–Henniart 1981, Proposition 1.1 and
Corollary 1.3(i) (printed pp. 93–94, PDF pp. 5–6), for the published
fixed-Haar epsilon expression of a single p-adic field. Let `χ` be a wildly
ramified character, and `η` a character of smaller conductor. Then the epsilon
expression of `χη` equals that of `χ`, times `η(a⁻¹)` for a linearizing
element `a` of `χ`, up to a root of unity of `p`-power order. This is the
rank-one input of the approximate-witness clause of `VirtualStabilityStatement`
(DH81 4.2(i), via 4.3–4.4).

Throughout, `G` is a p-adic field with topological data `T`. Characters are
quasicharacters of `G^×`. `ψ` is a unitary additive character with conductor
`n(ψ) = T.additiveConductor ψ`. `a(·)` is `T.multiplicativeConductor`, and
`ord` is `T.ord`. `T.additiveLattice j` is the set of elements of order at
least `-j`. `U^n` is `T.principalUnits n`. The epsilon expression is
`T.abelianEpsilonExpression`.

## Auxiliary facts

- `multiplicativeConductor_mul_of_lt`: if `a(η) < a(χ)`, then
  `a(χη) = a(χ)`.
- `exists_pow_eq_one_of_mem_principalUnits_one`: let `w ∈ U^1` and
  `a(χ) ≤ N + 1`. Then `χ(w)^(p^N) = 1`. Proof: `w^(p^N) ∈ U^(N+1)`, by
  `pow_prime_pow_mem_principalUnits` of the helper module
  `DeligneHenniartApproximateCoset`.
- `additive_pow_eq_one`: let `b` have order at least `-(n(ψ) + j)` and
  `j ≤ N`. Then `ψ(b)^(p^N) = 1`, because `p^N b` has order at least
  `-n(ψ)`.

## The Gauss integral (DH81 (1.1.1))

`gauss_integral_twist_shift` makes these assumptions:

- `a = m + k` with `0 < k ≤ m`;
- `d` has order `-(n(ψ) + a)` and linearizes `χ` at depth `m`, i.e.
  `χ(1 + y) = ψ(d y)` for `y` of order at least `m`;
- `b` linearizes `η` at depth `k`;
- `w = 1 + b/d` lies in `U^1`.

Then the Gauss integral of `χη` over the shell of order `-(n(ψ) + a)` equals

`(χη)(w)⁻¹ · η(d)⁻¹ · ψ(b)`

times the Gauss integral of `χ` over the same shell. With `w = 1 + b/a`, this
is DH81 (1.1.1). The proof:

1. `d + b = d w` linearizes `χη` at depth `m`.
2. The published `gauss_integral_localized` cuts both integrals down to the
   cosets `x ∈ (d + b) + T.additiveLattice (n(ψ) + m)` and
   `x ∈ d + T.additiveLattice (n(ψ) + m)`.
3. Rotation by the unit `w` (published `setIntegral_gaussShell_mul_unit`)
   carries the second coset onto the first.
4. On the coset, write `x = d v` with `v ∈ U^k`. The published
   `localized_ratio_mem` provides this. The two integrands then differ by the
   factor `(χη)(w)⁻¹ η(d)⁻¹ ψ(b) · η(v)⁻¹ ψ(b (v - 1))`. The last two factors
   cancel because `b` linearizes `η` at depth `k`.

DH81 handles the parities of `a(χ)` separately; this argument does not need
to.

## The epsilon expression (DH81 1.3(i))

- `abelianEpsilonExpression_mul_shift` assumes:
  - `a(χ) ≥ 2` and `a(η) < a(χ)`;
  - `d` has order `-(n(ψ) + a(χ))` and linearizes `χ` at depth
    `a(χ) - ⌊a(χ)/2⌋` (the hypothesis `hlin` of the published
    `RankOneStability.gauss_integral_twist`).

  Then for every Haar measure there is `N` with

  `abelianEpsilonExpression (χη)^(p^N) = (η(d⁻¹) · abelianEpsilonExpression χ)^(p^N)`.

  Proof: take `k = ⌊a/2⌋` and `m = a - k`. The element `b` is `0` if
  `a(η) ≤ k`. Otherwise it comes from the published
  `RankOneStability.exists_deep_linearization`, which applies because
  `a(η) ≤ a - 1 ≤ 2k`, and has order `-(n(ψ) + a(η))`. In both cases `b`
  has order at least `-(n(ψ) + a - 1)`. Hence `w = 1 + b/d ∈ U^1`. The
  published `deligneConstant_eq_abelianEpsilonExpression` turns the Gauss
  identity into an identity of epsilon expressions; it uses `a(χη) = a(χ)`.
  With `N = a`, the factors `(χη)(w)` and `ψ(b)` become `1` after raising to
  the power `p^N`.
- `abelianEpsilonExpression_mul_shift_of_comparison`: the same conclusion,
  with `η(c⁻¹)` in place of `η(d⁻¹)`, for any unit `c` with `c d⁻¹ ∈ U^1`.
  Here `η(d c⁻¹)` is a `p`-power root of unity.

## The approximate witness

- `ApproximateTwistWitness T χ ψ γ` (definition, a proposition): for every
  character `η` with `a(η) < a(χ)` and every Haar measure `μ`, there is `N`
  with `abelianEpsilonExpression (χη) ψ μ ^ (p^N) =
  (η(γ) · abelianEpsilonExpression χ ψ μ) ^ (p^N)`. This is the rank-one form
  of DH81 (4.2.1). The tests `η - 1` with `α(η) < α(χ)` are the
  dimension-zero virtual characters of 4.2 whose break is smaller than that of
  `χ`.
- `approximateTwistWitness_of_comparison`: under the hypotheses of
  `abelianEpsilonExpression_mul_shift`, `c⁻¹` is an approximate twist witness
  whenever `c d⁻¹ ∈ U^1`.
- `exists_approximateTwistWitness`: if `a(χ) ≥ 2`, there is an approximate
  twist witness `γ` of order `a(χ) + n(ψ)`. It is the inverse of the
  linearizer from `exists_deep_linearization`. This is DH81 4.2(i) and
  (4.2.2) in dimension one.

## Scope

The module is about a single p-adic field. It does not compare linearizers
across extensions; that is DH81 4.4 with 3.12(i). It does not prove the
approximate clause of `VirtualStabilityStatement`.
