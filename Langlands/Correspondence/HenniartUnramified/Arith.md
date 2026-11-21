# Counting lemmas for unramified descent

## Cardinalities

- `encard_eq_of_rel`: let a relation `R` between sets `S` and `T` be total in both
  directions, functional on `S`, and injective. Then `S` and `T` have the same extended
  cardinality. A choice function from `S` to `T` is a bijection, and `Set.encard_congr`
  applies.
- `encard_eq_mul_of_fibers`: suppose every element of `S` is related to some element of
  `T`, and the relation is functional on `S`. Suppose also that for every element of
  `T` the related elements of `S` are exactly the values of an injective family
  `Fin f → S`. Then `encard S = encard T * f`. The families give a bijection
  `T × Fin f ≃ S`. Both sides are computed in `ℕ∞`, so infinite sets are allowed.

## Möbius inversion

`moebius_count` takes a finset `Z` of elements of a type `α` and a function `mp : α → ℕ`. For `f > 0` it
proves, in `ℤ`,
`#{x ∈ Z | mp x = f} = Σ_{i ∣ f} μ(f/i) · #{x ∈ Z | mp x ∣ i}`.
For every `n > 0`, `#{mp ∣ n}` is the sum over the divisors `d` of `n` of `#{mp = d}`,
by fiberwise counting. Mathlib's `sum_eq_iff_sum_mul_moebius_eq` then inverts this.

## Polar counts

`polar_moebius` assumes that `q` is a prime power, `n, f ≥ 1`, `f ∣ n` and `f ∣ s`. It
proves
`f · ν(n, f, s; q) = Σ_{i ∣ f} μ(f/i) · τ(n/f, s/f; q^i)` in `ℤ`,
where `ν = polarPartCount` and `τ = polarTwistCount = ν(·, 1, ·; ·)`. Both sides are
evaluated with the published `polarPartClosedFormula`:

- For `s ≥ 1`, the closed formula with `f = 1` and parameter `q^i` is the inner factor
  `(q^i − 1)² Σ_e μ(e) q^{i(s/f/e − 1)}` of the general formula.
- For `s = 0` and `f ≠ n`, both sides vanish, since `n/f ≠ 1`.
- For `s = 0` and `f = n`, the term `τ(1, 0; q^i)` is `q^i − 1`.

`polar_moebius_of_le` removes the prime-power hypothesis. If `q` is not a prime power,
then neither is any `q^i` with `i ≥ 1`, and both sides are `0` by the definition of
`polarPartCount`.

These identities are the arithmetic part of route note Lemma `lem:nu` combined with
Proposition `prop:unram` (Henniart 1988, Proposition 2.2).
