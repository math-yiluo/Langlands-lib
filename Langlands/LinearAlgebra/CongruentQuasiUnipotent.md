# Congruent quasi-unipotent endomorphisms are unipotent

The module `Langlands.LinearAlgebra.CongruentQuasiUnipotent` proves a lemma of
Minkowski–Serre type for endomorphisms of modules.

## Main theorem

`isNilpotent_sub_one_of_isNilpotent_pow_sub_one` takes:

- a commutative ring `R`, an `R`-module `M` and a prime `ℓ` (`Fact ℓ.Prime`);
- `htf`: `M` has no `ℓ`-torsion, that is `ℓ • x = 0` implies `x = 0`;
- `hsep`: an element `x` of `M` such that for every `j` there is `y` with
  `x = ℓ ^ j • y` is zero;
- a natural number `a` with `3 ≤ ℓ ^ a`;
- an endomorphism `σ` of `M` with `ValuesDivisible (ℓ ^ a) (σ - 1)`, that
  is, every value `σ x - x` is `ℓ ^ a` times an element of `M`;
- a natural number `m > 0` such that `σ ^ m - 1` is nilpotent.

It concludes that `σ - 1` is nilpotent. In words: an endomorphism that is
congruent to the identity modulo `ℓ ^ a ≥ 3` and has a unipotent positive
power is unipotent. The scalar ring `R` plays no role beyond linearity; the
congruence and the divisibility hypotheses use natural-number multiples.

For a prime `ℓ`, `3 ≤ ℓ ^ a` means `a ≥ 1` and either `ℓ` is odd or
`a ≥ 2`. The bound is needed: `σ = -1` on `M = ℤ_2` is congruent to `1`
modulo `2`, satisfies `σ ^ 2 = 1` and is not unipotent.

## Proof

`ValuesDivisible k f` says that every value of `f` is `k` times an element
of `M`. The namespace `ValuesDivisible` proves that this condition is
closed under sums, negation, finite sums, and composition with any
endomorphism on either side. It also proves that it is multiplicative
(`mul`), that it passes to divisors of `k` (`of_dvd`), and that it is
compatible with natural-number multiples (`nsmul`). If `σ ≡ 1` modulo
`k`, then `σ ^ i ≡ 1` (`pow_sub_one`, by
`σ ^ (i + 1) - 1 = σ (σ ^ i - 1) + (σ - 1)`). Then
`1 + σ + ⋯ + σ ^ (m - 1) ≡ m` (`geomSum_sub`), since the difference is
`∑_{i < m} (σ ^ i - 1)`.

Two general facts drive the argument.

- `injective_of_ker_subset`: if every element of the kernel of `S` lies in
  `ℓ • M`, then `S` is injective. An element `x` of the kernel is `ℓ • y`.
  Then `ℓ • S y = 0`, so `S y = 0` because `M` has no `ℓ`-torsion. By
  induction `x` is divisible by every power of `ℓ`, so `x = 0` by `hsep`.
- `isNilpotent_of_isNilpotent_mul`: if `X` commutes with an injective `S`
  and `X * S` is nilpotent, then `X` is nilpotent. From
  `(X * S) ^ N = S ^ N * X ^ N = 0` and the injectivity of `S ^ N`,
  `X ^ N = 0`.

Write `X = σ - 1` and `S = 1 + σ + ⋯ + σ ^ (m - 1)`, so that
`X * S = σ ^ m - 1` (Mathlib's `mul_geom_sum`). `X` and `S` commute
(`commute_sub_one_geomSum`). It remains to show that `S` is injective,
which is done in two steps.

- Prime-to-`ℓ` step, `isNilpotent_sub_one_of_coprime`: assume `σ ≡ 1`
  modulo `ℓ` and `m = c` is coprime to `ℓ`. If `S x = 0`, then
  `S - c ≡ 0` modulo `ℓ` gives an element `z` with `-(c • x) = ℓ • z`,
  that is, `c • x = ℓ • (-z)`. A Bézout relation `u c + v ℓ = 1` over the
  integers then gives
  `x = u • (c • x) + ℓ • (v • x) = ℓ • (u • (-z) + v • x)`. So the kernel
  of `S` lies in `ℓ • M`, and `S` is injective.
- `ℓ` step, `isNilpotent_sub_one_of_pow_prime`: assume `σ ≡ 1` modulo
  `ℓ ^ a` with `3 ≤ ℓ ^ a`, and `m = ℓ`. Put
  `G i = 1 + σ + ⋯ + σ ^ (i - 1)` and `t = ∑_{i < ℓ} i`. Then
  `S - ℓ = ∑_{i < ℓ} (σ ^ i - 1) = X * ∑_{i < ℓ} G i`
  `= t • X + X * ∑_{i < ℓ} (G i - i)`.
  The second term is divisible by `ℓ ^ a * ℓ ^ a`, hence by `ℓ ^ 2`.
  For the first, `t * ℓ ^ a` is divisible by `ℓ ^ 2`. If `a ≥ 2` this
  holds trivially. If `a = 1`, then `ℓ` is odd, and `2 t = ℓ (ℓ - 1)`
  (Mathlib's `Finset.sum_range_id_mul_two`) shows that `ℓ` divides `t`.
  Hence `S ≡ ℓ` modulo `ℓ ^ 2`. If `S x = 0`, this gives an element `z`
  with `-(ℓ • x) = ℓ ^ 2 • z`, that is, `ℓ • (x - ℓ • (-z)) = 0`, so
  `x = ℓ • (-z)` because `M` has no `ℓ`-torsion. The kernel of `S` lies
  in `ℓ • M`, and `S` is injective.

`isNilpotent_sub_one_of_pow_prime_pow` iterates the `ℓ` step, using
`σ ^ ℓ ^ (k + 1) = (σ ^ ℓ) ^ ℓ ^ k` and `σ ^ ℓ ≡ 1` modulo `ℓ ^ a`. For the
main theorem write `m = ℓ ^ k * c` with `c` prime to `ℓ`
(`Nat.exists_eq_pow_mul_and_not_dvd`). The prime-to-`ℓ` step, applied to
`σ ^ ℓ ^ k` with exponent `c`, shows that `σ ^ ℓ ^ k` is unipotent. The
iterated `ℓ` step then shows that `σ` is unipotent.

## Provenance

The lemma is derived, as a quasi-unipotent variant of results of
Minkowski–Serre type. Two such results are in the literature:

- Silverberg and Zarhin, *Semistable reduction and torsion subgroups of
  abelian varieties*, Ann. Inst. Fourier 45 (1995), §4, printed p. 406,
  Theorem 4.1: let `n` be a positive integer and `O` an integral domain of
  characteristic zero in which no rational prime dividing `n` is a unit.
  An element `α` of `O` of finite multiplicative order with
  `α - 1 ∈ n O` satisfies `α = 1` if `n ≥ 3`, and `α ^ 2 = 1` if `n = 2`.
  The hypothesis on the primes dividing `n` cannot be dropped: in
  `O = ℤ[1/3]` with `n = 6`, the element `α = -1` has order two and
  `α - 1 = 6 · (-1/3)` lies in `6 O`.
- SGA 7 I, Exposé IX, Lemme 4.7.1 (due to Serre), proved in 4.7.3: let
  `G` be a commutative group scheme over a field that is an extension of
  an abelian scheme by a torus, and `n ≥ 2` an integer. An automorphism of
  `G` of finite order inducing the identity on the `n`-torsion subgroup
  scheme `ₙG` is the identity if `n ≠ 2`, and is the identity or of order
  two if `n = 2`.

The lemma here concerns instead an endomorphism of a module without
`ℓ`-torsion and without nonzero elements divisible by every power of `ℓ`,
congruent to the identity modulo `ℓ ^ a ≥ 3`. Finite order is replaced by
"some positive power is unipotent", and the conclusion is unipotence. The
argument through the geometric sum `1 + σ + ⋯ + σ ^ (m - 1)` is an
elementary replacement for the cyclotomic argument of 4.7.3. The lemma is
used in `Langlands/AbelianScheme/RaynaudSemiabelianCriterionReduction.lean`,
which derives Raynaud's criterion of semistable reduction from the Galois
criterion and the quasi-unipotence of inertia.
