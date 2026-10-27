# Proof of the prime-order orbit product expansion

Worker 807 wrote this module and this explanation. It proves the published
proposition `Langlands.LocalClassField.PrimeOrbitProductTraceExpansion.{u,v}`
from `Langlands.ClassFieldTheory.Local.PrimeOrbitProductTraceExpansionStatement`.
Workers 107 and 726 wrote that statement; this module imports it by name and
does not change it.

The main theorem is

```lean
theorem Langlands.LocalClassField.primeOrbitProductTraceExpansion :
    PrimeOrbitProductTraceExpansion.{u, v}
```

Its type is exactly the published proposition, and it adds no hypotheses. The
universes `u` and `v` stay arbitrary and independent. The proof uses only
`propext`, `Classical.choice` and `Quot.sound`.

## What is proved

Take a finite group `G` of prime order `p = Fintype.card G` with a given
`MulSemiringAction` on a commutative ring `R`, an ideal `I` with
`g • y ∈ I` for all `g` and all `y ∈ I`, and `x ∈ I`. The theorem constructs
`z ∈ I ^ 2` with

```text
(∏ g, (1 + g • x)) - 1 - (∑ g, g • x) - (∏ g, g • x) = ∑ g, g • z.
```

Here `z` is the sum of `∏ g ∈ S, g • x`, with one subset `S` of `G` taken from
each orbit of left translation on the subsets with between `2` and `p - 1`
elements. The proof never divides by `p` and uses no field, unit or
characteristic assumption. It covers the zero ring, `p = 2` (no such subsets,
and `z = 0`), `x = 0` and `I = ⊤`, because none of these cases needs special
treatment.

## Notation

`open scoped Pointwise` supplies Mathlib's action of `G` on `Finset G` by left
translation, `k • S = S.image (k • ·)`. Since `G` acts on itself by
multiplication, `k • g = k * g`. The proof works under `classical`, which
supplies the decidable equality that this action and `Finset` operations need.

## Helper results

Four helper theorems are in the namespace
`Langlands.LocalClassField.PrimeOrbitProductTraceExpansionProof`.

### `exists_mem_sum_eq_sum_smul`: sums over free orbits are orbit sums

Let a finite group `G` act on a type `β`, and distributively on an additive
commutative monoid `M`. Let `F : β → M` satisfy `F (g • b) = g • F b`, let `P`
be an additive submonoid of `M`, and let `s : Finset β` satisfy:

- `s` is invariant: `b ∈ s` implies `g • b ∈ s`;
- every orbit map on `s` is injective: for `b ∈ s`, `g • b = h • b` implies
  `g = h`;
- `F b ∈ P` for every `b ∈ s`.

Then some `z ∈ P` satisfies `∑ b ∈ s, F b = ∑ g, g • z`.

The proof is strong induction on `s` (`Finset.strongInduction`). If `s` is
empty, take `z = 0`. Otherwise pick `b ∈ s` and let `O` be the image of
`g ↦ g • b` over all of `G`. Then:

- `O ⊆ s` by invariance, and `b = 1 • b ∈ O`, so `s \ O` is a proper subset of
  `s`;
- `s \ O` is invariant: if `c ∈ s \ O` and `g • c = h • b`, then
  `c = (g⁻¹ * h) • b ∈ O`, a contradiction;
- the induction hypothesis on `s \ O` gives `z' ∈ P` with
  `∑ c ∈ s \ O, F c = ∑ g, g • z'`;
- since `g ↦ g • b` is injective, `Finset.sum_image` and equivariance give
  `∑ c ∈ O, F c = ∑ g, F (g • b) = ∑ g, g • F b`.

Splitting the sum over `s` at `O` (`Finset.sum_sdiff`) and using `smul_add`
then gives the claim with `z = F b + z'`, which lies in `P` because
`F b ∈ P` and `z' ∈ P`. Unfolding the induction, `z` is the sum of `F` over
one chosen point of each orbit in `s`. The induction replaces an explicit
choice of orbit representatives.

### `smul_finset_injective_of_prime_card`: translation is free on proper subsets

If `Fintype.card G` is prime and `S : Finset G` satisfies
`0 < S.card < Fintype.card G`, then `g • S = h • S` implies `g = h`.

From `g • S = h • S`, the element `h⁻¹ * g` lies in the stabilizer
`MulAction.stabilizer G S`. A subgroup of a group of prime order is `⊥` or `⊤`
(`Subgroup.eq_bot_or_eq_top_of_prime_card`, applied after rewriting
`Nat.card G` as `Fintype.card G`).

- If the stabilizer is `⊥`, then `h⁻¹ * g = 1`, so `g = h`.
- If it is `⊤`, choose `a ∈ S`, which exists because `S` is nonempty. Every
  `t : G` equals `(t * a⁻¹) • a`, and `(t * a⁻¹) • S = S`, so `t ∈ S`. Hence
  `S = univ`, and `S.card = Fintype.card G` contradicts the hypothesis.

### `prod_smul_mem_sq`: products over at least two elements lie in `I ^ 2`

If `I` is invariant, `x ∈ I` and `2 ≤ S.card`, then `∏ g ∈ S, g • x ∈ I ^ 2`.
`Finset.one_lt_card` gives distinct `a, b ∈ S`. Two applications of
`Finset.mul_prod_erase` write the product as
`((a • x) * (b • x)) * r`, where `r` is the product over `(S.erase a).erase b`.
Here `a • x` and `b • x` lie in `I` by invariance, so their product lies in
`I * I = I ^ 2` (`Ideal.mul_mem_mul`, `sq`). Multiplying by `r` stays in the
ideal (`Ideal.mul_mem_right`).

### `prod_smul_smul_finset`: the product is equivariant

For `k : G` and `S : Finset G`,
`∏ g ∈ k • S, g • x = k • ∏ g ∈ S, g • x`. Write `k • S` as the image of
`S` under the injective map `g ↦ k * g` (`Finset.smul_finset_def`,
`Finset.prod_image`). Then use `(k * g) • x = k • (g • x)` (`mul_smul`) and
the fact that `k` acts multiplicatively on `R` (`Finset.smul_prod'`, from
the `MulDistribMulAction` underlying the `MulSemiringAction`).

## The main proof

Let `p = Fintype.card G` and let `mid S` mean `2 ≤ S.card ∧ S.card < p`.

1. **The witness.** Apply `exists_mem_sum_eq_sum_smul` with `β = Finset G` under
   left translation, `M = R`, `F S = ∏ g ∈ S, g • x`,
   `P = (I ^ 2).toAddSubmonoid` and `s = univ.filter mid`. The hypotheses
   hold for these reasons:
   - equivariance is `prod_smul_smul_finset`;
   - `s` is invariant because translation preserves cardinality
     (`Finset.card_smul_finset`);
   - orbit maps on `s` are injective by `smul_finset_injective_of_prime_card`,
     since `mid S` gives `0 < S.card < p`;
   - `F S ∈ I ^ 2` by `prod_smul_mem_sq`, since `2 ≤ S.card`.

   This yields `z ∈ I ^ 2` with `∑ S ∈ univ.filter mid, F S = ∑ g, g • z`.
2. **Expansion.** `Finset.prod_one_add` and `Finset.powerset_univ` rewrite
   `∏ g, (1 + g • x)` as `∑ S : Finset G, F S`.
   `Finset.sum_filter_add_sum_filter_not` splits this sum into the sum over
   `univ.filter mid` and the sum over the subsets with `¬ mid S`.
3. **The remaining subsets.** The subsets with `¬ mid S` are exactly `∅`,
   `univ` and the singletons `{a}`, as a `Finset` equality:
   - `S.card < 2` gives `S.card = 0` (`S = ∅`) or `S.card = 1`
     (`S = {a}`, by `Finset.card_eq_one`);
   - `p ≤ S.card` together with `S.card ≤ p` gives `S = univ`
     (`Finset.eq_univ_of_card`);
   - conversely, `∅` and `{a}` have fewer than two elements, and `univ` has
     `p` elements.

   These pieces do not overlap. `∅ ≠ univ` because `G` is nonempty, `∅` is not
   a singleton, and `{a} ≠ univ` because `p ≥ 2` (`Nat.Prime.two_le`). The
   singleton map is injective, so the remaining sum is
   `F ∅ + (F univ + ∑ a, F {a}) = 1 + (∏ g, g • x + ∑ a, a • x)`
   (`Finset.sum_insert`, `Finset.sum_image`, `Finset.prod_empty`,
   `Finset.prod_singleton`).
4. **Conclusion.** The left side of the target equality therefore equals
   `∑ S ∈ univ.filter mid, F S`, which is `∑ g, g • z` by step 1. The final
   rearrangement is done by `abel`.

## Relation to the source

The statement Markdown records the source: Serre, *Local Fields* (1979),
Chapter V, §3, Lemma 5 and its proof, printed pp.83–84. Serre expands
`∏_s (1 + x^s)` over sums of distinct elements of the cyclic group `G`. He then
notes that the translates of a sum with `2 ≤ k ≤ l - 1` terms are distinct, so
their contributions together form a trace. This module formalizes that subset
argument in the generality of the published proposition. It differs from the
printed proof in two ways:

- freeness of translation on proper nonempty subsets comes from the
  subgroup dichotomy for groups of prime order, not from a chosen
  generator;
- the trace of a representative product is the orbit sum `∑ g, g • z`. The
  representatives are chosen implicitly by the strong induction in
  `exists_mem_sum_eq_sum_smul`.

The module proves only the ring-level identity. It contains no field norm or
trace, and it does not specialize to an integer ring or a maximal ideal.
