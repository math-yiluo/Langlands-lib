# Proof of finite-order detection modulo an integer

`Langlands/Algebra/FiniteOrderCongruenceProof.lean` proves the published
proposition `Langlands.FiniteOrderCongruenceDetectionStatement.{u}` from
`Langlands.Algebra.FiniteOrderCongruenceStatement`. The main theorem is

```lean
theorem Langlands.FiniteOrderCongruence.finiteOrderCongruenceDetection :
    FiniteOrderCongruenceDetectionStatement.{u}
```

It holds in every universe `u`, with no hypotheses beyond the statement's own,
and its axioms are `propext`, `Classical.choice` and `Quot.sound`. The proof is
self-contained: it imports only the statement module and Mathlib
(`Mathlib.Data.Nat.Choose.Dvd`, `Mathlib.RingTheory.Filtration`,
`Mathlib.RingTheory.Coprime.Lemmas`, `Mathlib.Tactic.NoncommRing`). All
auxiliary results are in the namespace `Langlands.FiniteOrderCongruence`.

## Mathematical outline

Let `M` be finitely generated, `n ≥ 3`, every torsion element of `M` killed by
`n`, and `σ` an automorphism of finite order with `σ x - x ∈ nM` for all `x`.

1. Choose a prime `p` and `a ≥ 1` with `p ^ a ∣ n` and `p ≥ 3` or `a ≥ 2`.
2. The subgroup `N = nM` is finitely generated and torsion-free, and `σ`
   preserves it. On `N`, `σ - 1` takes values in `nN`, hence in `p ^ a N`.
3. A core lemma about torsion-free groups (below) shows that `σ` is the
   identity on `N`.
4. For `x : M` write `σ x = x + n • y`. Then
   `n • (n • y) = σ (n • x) - n • x = 0`, so `y` is torsion, so `n • y = 0` and
   `σ x = x`.

The route agrees with the strategy recorded in the statement's Markdown: pass
to a torsion-free part and use that the difference from the identity is
torsion-valued. Where Conrad's argument cites the torsion-freeness of a
principal congruence kernel of `GL_d(ℤ)`, this proof gives a direct argument
for an endomorphism ring with a `p`-adic filtration.

## The filtration on endomorphisms

For an additive commutative group `F`, natural numbers `p` and `k`, the
definition

```lean
def fil (p k : ℕ) : AddSubgroup (AddMonoid.End F)
```

is the additive subgroup of endomorphisms `x` such that every `x v` has the
form `p ^ k • w` (`mem_fil`). The ring structure of `AddMonoid.End F` is
composition. The basic lemmas are:

- `fil_mono`: `fil F p k ≤ fil F p j` for `j ≤ k`;
- `mul_mem_fil`: `fil j * fil k ⊆ fil (j + k)`. Also `mul_mem_fil_left` and
  `mul_mem_fil_right` (the `fil k` are two-sided ideals), and the special case
  `natCast_mul_mem_fil`;
- `prime_mul_mem_fil`: `p * fil k ⊆ fil (k + 1)`;
- `pow_mem_fil`: `x ∈ fil a → x ^ i ∈ fil (a * i)`;
- `mem_fil_of_prime_mul_mem`: if `F` is torsion-free, `p ≠ 0` and
  `p * x ∈ fil (k + 1)`, then `x ∈ fil k`. This divides by `p` using Mathlib's
  `nsmul_right_injective`;
- `eq_zero_of_forall_mem_fil`: if `F` is torsion-free and finitely generated
  (`Module.Finite ℤ F`), `p` is prime and `x ∈ fil k` for every `k`, then
  `x = 0`. This is Krull's intersection theorem, Mathlib's
  `Ideal.iInf_pow_smul_eq_bot_of_isTorsionFree`, applied to the proper ideal
  `(p)` of `ℤ`: each value `x v` lies in `⋂ₖ (p) ^ k • F = 0`.

## Binomial congruences

`one_add_pow_sub_mem` proves, for `x ∈ fil a` and every `m`,

```text
(1 + x) ^ m - 1 - m * x - C(m, 2) * x ^ 2 ∈ fil (a * 3).
```

The proof is by induction on `m`. The identity

```text
E(m + 1) = E(m) * (1 + x) + C(m, 2) * x ^ 3,
```

where `E(m)` is the left-hand side, follows from Pascal's rule
`C(m + 1, 2) = m + C(m, 2)` and `noncomm_ring`, because `x` commutes with `1`.
Both summands lie in `fil (a * 3)`. `one_add_pow_sub_one_mem` deduces
`(1 + x) ^ m - 1 ∈ fil a`.

## The descent step

`mem_fil_succ`: let `F` be torsion-free, `p` prime, `1 ≤ a` and
`3 ≤ p ∨ 2 ≤ a`. Let `ℓ` be a prime, `x ∈ fil a` and `(1 + x) ^ ℓ = 1`. Then
`x ∈ fil (a + 1)`.

From the binomial congruence and `(1 + x) ^ ℓ = 1`,
`ℓ * x + C(ℓ, 2) * x ^ 2 ∈ fil (a * 3)`, and `x ^ 2 ∈ fil (a * 2)`.

- If `ℓ = p`, then `C(p, 2) * x ^ 2 ∈ fil (a + 2)`. When `p ≥ 3`, `p` divides
  `C(p, 2)` (`Nat.Prime.dvd_choose_self`), giving `fil (2a + 1)`. When `a ≥ 2`,
  `2a ≥ a + 2` already suffices. Since `3a ≥ a + 2`, subtraction gives
  `p * x ∈ fil (a + 2)`, and dividing by `p` gives `x ∈ fil (a + 1)`.
- If `ℓ ≠ p`, subtraction gives `ℓ * x ∈ fil (2a) ⊆ fil (a + 1)`. Clearly
  `p ^ (a + 1) * x ∈ fil (a + 1)`. Bézout for the coprime integers `ℓ` and
  `p ^ (a + 1)` writes `1 = u ℓ + w p ^ (a + 1)`, so
  `x = u * (ℓ * x) + w * (p ^ (a + 1) * x) ∈ fil (a + 1)`.

## Core lemma

`eq_one_of_sub_one_mem_fil`: let `F` be torsion-free and finitely generated,
`p` prime, `1 ≤ a` and `3 ≤ p ∨ 2 ≤ a`. Let `g : AddMonoid.End F` satisfy
`g - 1 ∈ fil a` and `g ^ m = 1` for some `m > 0`. Then `g = 1`.

The proof is strong induction on `m`. If `m = 1` there is nothing to prove.
Otherwise let `ℓ = m.minFac` (a prime) and `m' = m / ℓ`, so `0 < m' < m`.
Then `x = g ^ m' - 1 ∈ fil a` by `one_add_pow_sub_one_mem`, and
`(1 + x) ^ ℓ = g ^ m = 1`. Repeating `mem_fil_succ` gives `x ∈ fil (a + k)` for
all `k`, so `x ∈ fil k` for all `k`, and `x = 0` by `eq_zero_of_forall_mem_fil`.
Thus `g ^ m' = 1`, and the induction hypothesis gives `g = 1`.

## Choice of the prime power

`exists_prime_pow_dvd`: every `n ≥ 3` has a prime `p` and `a ≥ 1` with
`p ^ a ∣ n` and `3 ≤ p ∨ 2 ≤ a`. If `4 ∣ n`, take `p = 2` and `a = 2`.
Otherwise `n` or `n / 2` is an odd divisor `m ≥ 2` of `n`, and
`p = m.minFac` is an odd prime with `a = 1`.

## The main theorem

In `finiteOrderCongruenceDetection`, `N` is the range of the endomorphism
`(n : AddMonoid.End M)`, that is `nM`. In the proof:

- `N` is torsion-free (`htfN`). If `k ≠ 0` and `k • (v₁ - v₂) = 0` with
  `v₁ - v₂ = n • y`, then `y` is killed by `k * n > 0`, so `n • y = 0` by the
  torsion premise.
- `N` is finitely generated (`hfgN`), as the image of a homomorphism from a
  finitely generated group (`AddGroup.fg_range`,
  `Module.Finite.iff_addGroup_fg`).
- `σ` maps `N` into `N`, which defines `g : AddMonoid.End N`. Its powers agree
  with powers of `σ.toEquiv` in `Equiv.Perm M` (`hgpow`), so `g ^ r = 1`.
- `g - 1 ∈ fil N p a` (`hgfil`). With `n = p ^ a * c` and
  `σ y = y + n • z`, `σ (n • y) - n • y = p ^ a • (c • (n • z))`, and
  `c • (n • z) ∈ N`.
- The core lemma gives `g = 1`, so `σ (n • x) = n • x` for all `x`. The last
  step is item 4 of the outline, followed by extensionality of additive
  equivalences against `AddEquiv.refl M`.

## Scope

The theorem's type is exactly the published statement; no additional hypotheses
are assumed. The finite-order premise is used only for the restriction `g`,
and the torsion premise only for torsion-freeness of `nM` and in the final
step. The auxiliary declarations (`fil` and the lemmas above) are proof
infrastructure, not separate published targets.
