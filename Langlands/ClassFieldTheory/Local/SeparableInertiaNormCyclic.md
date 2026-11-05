# Unit norm surjectivity for a Galois extension of prime degree

Author: Worker 1512. This is the second helper module of the proof of
`Langlands.ClassFieldTheory.Local.SeparableInertiaUnitNormSurjectivity` (see
`SeparableInertiaNormProof.md`). It imports `SeparableInertiaNormHensel` and the
published module `Langlands.ClassFieldTheory.Local.PrimeOrbitProductTraceExpansionProof`.
From the latter it uses three group-action lemmas: `exists_mem_sum_eq_sum_smul`,
`prod_smul_smul_finset` and `smul_finset_injective_of_prime_card`.

All declarations are in `Langlands.ClassFieldTheory.Local.SeparableInertiaNorm`.

## Setting

`C / B` is a field extension and `w : Valuation C ℝ≥0`. The structure
`CyclicHyp w π` (an internal interface, not a literature statement) bundles:

- `inv`: `w (σ x) = w x` for every `σ : Gal(C/B)`;
- `prime`: `finrank B C` is a prime `p`;
- `hensel`, `residueRoot`: `ValHensel` and `ValResidueRoot` for the restriction
  `w.comap (algebraMap B C)`;
- `unif`: `π : B` is a `ValUniformizer` of that restriction;
- `res`: every integral `x : C` is congruent to some integral `c : B`, that is,
  `w (x - c) < 1`.

Write `γ = w π`, which satisfies `0 < γ < 1`. In the theorems after
`variable [FiniteDimensional B C] [IsGalois B C]`, the extension is finite
Galois of degree `p`.

## Results

- `exists_pow_mul_le`: for `γ < 1` and `0 < b`, some `γ ^ m * a ≤ b`.
- `valLE w r`: the additive submonoid `{y | w y ≤ r}`.
- `val_one_add`: `w z < 1` implies `w (1 + z) = 1`.
- `card_gal`: `Fintype.card Gal(C/B) = finrank B C`.
- Discreteness over `B`: `val_eq_pow` (nonzero integral elements of `B` have
  value `γ ^ k`), `le_pow_succ_of_lt` (a value of `B` below `γ ^ n` is at most
  `γ ^ (n + 1)`), and `eq_pow_of_lt_of_le`.
- `val_norm`: `w (N x) = w x ^ p`, from `Algebra.norm_eq_prod_automorphisms`
  and `inv`.
- `val_trace_le`: `w (Tr x) ≤ w x`, from `trace_eq_sum_automorphisms`.

### The norm expansion (`norm_one_add_expansion`)

For `x : C` there are coefficients `c : ℕ → B` such that, for every `b : B`,

`N(1 + b x) = ∑_{k = 0}^{p} c k * b ^ k`,

with `c 0 = 1`, `c 1 = Tr x` and `c p = N x`. Moreover, for `1 ≤ k < p`,
`c k = Tr z` for some `z` with `w z ≤ w x ^ k`, and `w (c k) ≤ w x ^ k` for
all `k`.

Proof. `N(1 + b x) = ∏_σ (1 + b σx)` expands by `Finset.prod_one_add` into
`∑_k b ^ k e_k`. Here `e_k` is the sum over the `k`-element subsets `S` of
`Gal(C/B)` of `∏_{g ∈ S} g x`. For `0 < k < p` the group acts freely on these
subsets, because a nontrivial subgroup of a group of prime order is the whole
group (`smul_finset_injective_of_prime_card`). Hence `e_k` is a sum of
`Gal(C/B)`-orbit sums, and `exists_mem_sum_eq_sum_smul` writes it as
`∑_g g z = Tr z` with `z` in `valLE w (w x ^ k)`. Each product `∏_{g ∈ S} g x`
has value `w x ^ k` by `inv`. The coefficients `c k` are defined casewise;
`c k = 0` for `k > p`.

### Total ramification (`exists_val_pow_eq`)

Some `πL : C` has `w πL ^ p = γ`. Suppose not. Then:

1. Every `y` with `w y < 1` has `w y ≤ γ`. By `val_norm`,
   `w y ^ p = γ ^ k`. If `p ∣ k`, then `w y` is a positive power of `γ`.
   Otherwise choose `a, b` with `k a = p b + 1`, so that `y ^ a / π ^ b` would
   be a `p`-th root of `γ`, which is a contradiction.
2. By `res`, every integral `x` is approximated by `c : B` with
   `w (x - c) ≤ γ ^ n` for every `n`, by induction on `n` using step 1.
3. Hence `w (σx - x) ≤ γ ^ n` for all `n`, so `σ x = x` for every `σ` and
   every integral `x`.
4. Scaling by a power of `π`, every element of `C` is fixed, so `C = B` by
   `IsGalois.mem_range_algebraMap_iff_fixed`. This contradicts `p ≥ 2`.

### Openness (`exists_open`)

There is `M` such that every `u : B` with `w (u - 1) ≤ γ ^ M` is `N x` for some
`x` with `w x = 1`. Take `x1` with `Tr x1 = 1` (`Algebra.trace_surjective`) and
`m` with `γ ^ m * w x1 ≤ 1`. Put `t = π ^ m` and `x0 = t x1`, so `x0` is
integral and `Tr x0 = t`. With `M = 2m + 1` and `a0 = (1 - u) / t ^ 2`, we have
`w a0 < 1`. The strong Hensel lemma `exists_root_one_add_of_hensel` solves

`a0 + y + ∑_{2 ≤ k ≤ p} (c k * t ^ (k - 2)) * y ^ k = 0`

with `w y < 1`, where `c` is the expansion for `x0`. Multiplying by `t ^ 2`
gives `N(1 + t y x0) = u`, and `1 + t y x0` is a unit by `val_one_add`.

### The approximation step

- `exists_witness` (level `n ≥ 1`): there is `w1` with `w w1 < 1` whose
  expansion has all coefficients `c k`, `1 ≤ k ≤ p`, of value at most `γ ^ n`,
  with at least one equal to `γ ^ n`. Let `δ = w πL`, so `δ ^ p = γ`.
  - If every `x` with `w x ≤ δ ^ n` has `w (Tr x) ≤ γ ^ n`, take `w1 = πL ^ n`.
    Its norm coefficient `c p` has value exactly `γ ^ n`.
  - Otherwise let `j` be the least index such that every `x` with
    `w x ≤ δ ^ j` has `w (Tr x) ≤ γ ^ n` (`Nat.find`; `j = p n` works). Then
    `j > n`, and minimality gives `x0` with `w x0 ≤ δ ^ (j - 1)` and
    `w (Tr x0) > γ ^ n`. Take `w1 = π x0`. Then `w w1 ≤ δ ^ j`, so the bound
    holds for all coefficients. Moreover `w (Tr w1) = γ w (Tr x0)` lies in
    `(γ ^ (n + 1), γ ^ n]`, hence equals `γ ^ n` by discreteness.
- `exists_improve`: if `w a = γ ^ n` with `n ≥ 1`, some unit `x` has
  `w (N x - (1 + a)) < γ ^ n`. Apply `ValResidueRoot` to
  `f = -1 + ∑_{1 ≤ k ≤ p} (c k / a) X ^ k` for the level-`n` witness. Its
  coefficients are integral and one of them has value `1`. The root `b` gives
  `x = 1 + b w1`, and `N x - (1 + a) = a f(b)`.
- `norm_claim_step`: if every `u` with `w (u - 1) ≤ γ ^ (n + 1)` is a unit norm,
  then so is every `u` with `w (u - 1) ≤ γ ^ n`. Either the stronger bound
  already holds, or `w (u - 1) = γ ^ n`; then `exists_improve` gives `x1`, and
  `u / N x1` satisfies the stronger bound.
- `norm_claim_zero`: if every `u` with `w (u - 1) ≤ γ` is a unit norm, then so
  is every unit `u`. `ValResidueRoot` applied to `X ^ p - u` gives a unit `b`
  with `w (b ^ p - u) < 1`, hence `w (u / b ^ p - 1) ≤ γ`. Then `u` is the norm
  of `x * b`, because `N b = b ^ p` for `b ∈ B`.

### Main theorem (`CyclicHyp.exists_norm_eq`)

Every `u : B` with `w u = 1` is `N x` for some `x : C` with `w x = 1`. From
`exists_open`, induction on `d` with `norm_claim_step` covers every level
`n ≥ 1` with `M ≤ n + d`. Then `norm_claim_zero` finishes the proof.

## Relation to the literature

Serre, *Local Fields* (literature ID `serre-1979-local-fields`), Chapter V,
§3 (printed pp. 83–86, PDF pp. 90–93) treats totally ramified cyclic
extensions of prime degree of complete discretely valued fields. Its Lemma 5
(printed p. 83) is the analogous expansion
`N(1 + x) ≡ 1 + Tr x + N x`, and its surjectivity results compare the graded
pieces of the unit filtrations. The Lean proof uses the same expansion and
the same level-by-level approximation. It never assumes completeness or total
ramification. Total ramification is derived (`exists_val_pow_eq`), and the
final passage to the limit is replaced by openness from the strong Hensel
lemma (`exists_open`).
