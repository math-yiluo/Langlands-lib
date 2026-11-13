# Approximate generators with approximate syzygies: Artin–Rees comparison

This module proves the Artin–Rees comparison used in the proof of Stacks
Project Lemma 98.10.1 (Tag 07XB, `artin.pdf`, printed pp. 14–16). Stacks applies
More on Algebra, Lemma 4.2 to two complexes `P^t → P^r → P` that agree modulo
`m^N` and concludes that the quotients have isomorphic associated graded rings.
This module proves the elementwise statement that the reduction actually uses:
initial forms of the approximate ideal are initial forms of the exact one. The
provenance is derived from that step. The argument and formulation are internal.

Throughout, `Q : Type u` is a commutative ring and `𝔫` an ideal of `Q`.
The generators are indexed by an arbitrary finite type `ι`, and the syzygy rows by
an arbitrary finite type `κ`.

## Artin–Rees for a finite family

`exists_artinRees_span` assumes `Q` is Noetherian, `M` is a finite `Q`-module,
`I` is an ideal and `v : ι → M` is a finite family. It gives a constant `c` such that for
every `n ≥ c`, every `x` in the span of `v` that lies in `I ^ n • M` can be written
as `∑ l, w l • v l` with every coefficient `w l` in `I ^ (n - c)`. The proof is
Mathlib's Artin–Rees lemma `Ideal.exists_pow_inf_eq_pow_smul` for the span of `v`,
followed by `Submodule.mem_ideal_smul_span_iff_exists_sum`.

## One improvement step

`exists_improved_coefficients` fixes generators `b : ι → Q`, rows
`K : κ → ι → Q`, approximations `b'`, `K'` and natural numbers `c₁`, `c₂`, `N`. Its
hypotheses are:

- the Artin–Rees conclusion with constant `c₁` for the ideal spanned by `b`;
- the Artin–Rees conclusion with constant `c₂` for the span of the rows of `K` in
  `ι → Q`;
- every relation `∑ j, u j * b j = 0` lies in the span of the rows of `K`;
- every row of `K'` is a relation of `b'`;
- `c₁ + 1 ≤ N`, `c₂ + 1 ≤ N`, and `b' j - b j` and `K' l j - K l j` lie in
  `𝔫 ^ N`.

If `m + N ≤ d`, `z ∈ 𝔫 ^ d` and `z = ∑ j, u j * b' j` with every `u j` in
`𝔫 ^ m`, then `z = ∑ j, u' j * b' j` with every `u' j` in `𝔫 ^ (m + 1)`.

The proof follows the coefficients. `y = ∑ u j * b j` differs from `z` by
`∑ u j * (b' j - b j) ∈ 𝔫 ^ (m + N)`, so `y` lies in `(b) ∩ 𝔫 ^ (m + N)`. Artin–Rees writes
`y = ∑ v j * b j` with `v j ∈ 𝔫 ^ (m + N - c₁)`. Then `u - v` is a relation of `b`
whose coordinates lie in `𝔫 ^ m`. Artin–Rees for the rows writes it as
`∑ w l • K l` with `w l ∈ 𝔫 ^ (m - c₂)`. If `m < c₂`, any expression in the rows is
used and `m - c₂ = 0`. The new coefficients are `u - ∑ w l • K' l`; they represent the
same `z` because the rows of `K'` are relations of `b'`. Coordinatewise they equal
`v j - ∑ w l * (K' l j - K l j)`, which lies in `𝔫 ^ (m + 1)` by the bounds on `N`.

## The comparison

`exists_approximation_order` assumes `Q` is Noetherian and the rows of `K` generate
all relations of `b`. It gives `c` such that for every `N ≥ c + 1`, all `b'`
and `K'` with the rows of `K'` relations of `b'` and with
`b' ≡ b`, `K' ≡ K` modulo `𝔫 ^ N`, every `d`, and every
`z ∈ Ideal.span (Set.range b')` with `z ∈ 𝔫 ^ d`:

```text
z ∈ Ideal.span (Set.range b) ⊔ 𝔫 ^ (d + 1).
```

Here `c` is the maximum of the two Artin–Rees constants. The proof shows by
induction on `m` that either the conclusion holds or `z` has a representation with
coefficients in `𝔫 ^ m`. If `m + N ≤ d`, the improvement step applies. Otherwise
`z = ∑ u j * b j + ∑ u j * (b' j - b j)`, and the second sum lies in
`𝔫 ^ (m + N) ⊆ 𝔫 ^ (d + 1)`. At `m = d + 1` a representation puts `z` in `𝔫 ^ (d + 1)`.
