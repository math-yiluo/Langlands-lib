# Interlaced induction blocks: the case `A ≥ C`

Lean module: `Langlands.Representation.Archimedean.RealInterlacedProof`, namespace
`Langlands.Archimedean.RealInterlacedJacquet`.

Fifth of the six modules that prove `RealInterlacedInducedInducedLinkedJacquetFunctionalStatement`
(see `RealInterlacedMirror.md`). It imports `RealInterlacedEngine`. It proves the statement when
`|m(e)| ≤ |m(d)|` (`interlaced_AC`). The notation is that of the four earlier modules.

## Setting

Let `d, e` be the two induction blocks, `p = |m(d)|`, `q = |m(e)|`, and `s, t` their exponents. The
position exponents of `[induced d, induced e]` are
`(τ₀, τ₁, τ₂, τ₃) = (u₁, v₁, u₂, v₂) = (s + p/2, s - p/2, t + q/2, t - q/2)`. The hypothesis
`s - t = |p - q|/2 + k` with `1 ≤ k ≤ min(p, q)` gives, for `q ≤ p`,

* `A = u₁ - u₂ = p - q + k > 0`, `B = u₂ - v₁ = q - k ≥ 0`, `C = v₁ - v₂ = k > 0`, and
  `u₁ - v₁ = p`.

At `-1` the position characters take the values `(-1)^{p+1}, 1, (-1)^{q+1}, 1`
(`realInducedFirstCharacter_neg_one`, `realInducedSecondCharacter_neg_one`).

## Positions of `GL₄` (section Positions)

`ia40` … `ib42` and `sw40_0` … `sw42_3` evaluate the positions of the blocks `0, 1, 2` and the
transpositions `sw` of `RealCharacterCrossing`. `neg_one_pow_congr` and `neg_one_pow_mod_flip` are
parity identities for `(-1)^a` in `ℂ`.

## Fourier coefficients of the final functions (section Coefficients)

* `coeff_ne_zero_of_eq`: transport of a nonzero coefficient along a pointwise equality.
* `coeff_pair_neg_ne_zero`: for `c ≠ 0` and `s ≤ m`, the coefficient at `-(m - s)` of
  `t ↦ c (i e^{-it} + i)^m + (-1)^s c (i e^{-it} - i)^m` is nonzero. By `coeff_binom_pair` it is
  `2π C(m, s) c i^m (1 + 1)`.
* `coeff_pair_pos_ne_zero`: for `g ≠ 0`, `s ≤ 1` and `m > 0`, the coefficient at `(1 + s) mod 2`
  of `θ ↦ 2π g (i e^{iθ} + 1)^m - 2π g (-1)^s (-i e^{iθ} + 1)^m` is nonzero. It is `(2π)² g · 2im`
  for `s = 0` (mode `1`) and `(2π)² g · 2` for `s = 1` (mode `0`). One factor of `2π` is already
  in the function, and the other comes from the unnormalized coefficient integral in
  `coeff_binom_pair`.

## Multipliers (section Multipliers)

* `isRecurrent_sign_one`: `sgn` solves the recurrence for `δ = 1` on the odd class.
* `exists_tail_mult` (**the tail step**): for `B ≥ 0`, `ε = (B + 1) mod 2` and a mode `j` with
  `|j| > B` and `j ≡ ε`, there is a multiplier recurrent for `δ = 1 - B` on the class `ε`,
  symmetric for `(-1)^ε`, with `μ_j ≠ 0`. For `B > 0` it is the Library's `tailMultiplier`
  (`RealBlockMultiplier`), and for `B = 0` it is `sgn`.

## The case `A ≥ C` (section AC)

### Test functions

* `uA = e₁` and `uB = -e₀ - i e₂ - e₃` are the two columns. `colv_uA_one` and `w_one_AC` give
  their values at `1`: `w₁ = 1`, `w₂ = 1` and `w₃ = -i`.
* `values_AC_kappa`: along `r₁(t) r₀(π/2)` the functions take the values `yZ h40 uA = -1`,
  `yZb h40 uA = -1`, `ν₊ = i e^{-it} + i` and `ν₋ = i e^{-it} - i`.
* `yZ1_fl32`, `values_AC_rot2`: for `T = (yZ h41 uA)^r w₊^m`,
  `T(r₂(θ)) = (i e^{iθ} + 1)^m` and `T(s₃ s₂ r₂(θ)) = (-i e^{iθ} + 1)^m`.

### The engine `engine_AC`

Data: `r + m = p + 1`, `q ≤ m` and `m + q` odd. Two pieces are given as hypotheses:

* a real Jacquet functional `ψ₀ = ℓ_{μ₀}` at the block `2` on `[induced d, induced e]`. Its
  exponents `a₀` satisfy the four differences above, and its signs are
  `e₀ = ((p + 1) mod 2, 0, (q + 1 + k mod 2) mod 2, k mod 2)`. Its multiplier has
  `μ₀(m) = 1` and `μ₀(-m) = (-1)^{k mod 2}`;
* a multiplier `μ₁`, recurrent for `δ = 1 - B` on the class `(q + 1 + k) mod 2`, symmetric, with
  `μ₁(-(m - k mod 2)) ≠ 0`.

The chain is as follows.

1. `Ψ₀ = frobMap ψ₀` (flat: the exponents stay `(u₁, v₁, u₂, v₂)`).
2. `Ψ₁`: the Frobenius map of `ℓ_{μ₁}` at the block `1` (`isJacquet_cross`, `δ = v₁ - u₂ + 1`).
   The exponents become `(u₁, u₂, v₁, v₂)`.
3. `Ψ₂`: the Frobenius map of the Library's `genericMultiplier A ε₂` at the block `0`
   (`δ = A + 1`, `Re A > 0`). It has no zeros because `A ≡ ε₂ (mod 2)`. The exponents become
   `(u₂, u₁, v₁, v₂)`.
4. The dichotomy `exists_of_dichotomy` for `B = Ψ₂ Ψ₁ Ψ₀`. It is taken at the block `1`, with
   `k₁ = u₁ - v₁ = p`, and the final binomial functional is at the block `2`, with
   `k₂ = v₁ - v₂ = k`. The flipped signs are `e' = (e₀(2), p mod 2, 1, e₀(3))`. Then
   `par h42 e' = (1 + k mod 2) mod 2`.

The main hypothesis of the dichotomy comes from `main_value` as follows.

* The test vector `v` is given by `exists_test_of` for `G = Fp h40 uA uB r m`. Its sign exponents
  are `(r + m, 0, m, 0)` (`isSignEq_Fp0`), and its modes are `±(p + 1)` along `r₀` and `±m` along
  `r₂`.
* On `SO(4)`, `Ψ₀ v = H₁ = G₊ + (-1)^{k mod 2} G₋` (`frobMap_eq_two_mode` and `μ₀(±m)`). This is
  in `Sm uA uB r m`.
* `hval` holds at `κ₀ = r₀(π/2)` and `j* = -(m - k mod 2)`. By `values_AC_kappa` the function is
  the one of `coeff_pair_neg_ne_zero` with `c = (-1)^r` and `s = k mod 2`.
* The parity class of the middle block after the chain is `(p + 1) mod 2 = (r + m) mod 2`.
* `hfin` holds at `r_b = 2` and `j_f = (1 + k mod 2) mod 2`. The sign is
  `(-1)^{e₀(1) + e₀(3)} = (-1)^{k mod 2}`, so by `values_AC_rot2` the function is the one of
  `coeff_pair_pos_ne_zero`.

### The flat functional `exists_flat_AC`

For every `k` and `m > 0` there are `μ₀` and `e₀` such that `ℓ_{μ₀}` at the block `2` is a real
Jacquet functional with the exponents of `[induced d, induced e]`. The signs `e₀` are those of the
engine, and `μ₀(m) = 1`, `μ₀(-m) = (-1)^{k mod 2}`. For `k` even, `μ₀ = 1` with the natural
signs. For `k` odd, `μ₀ = sgn`, which is flat at the block `2` by `flat_sign` (the window of
weight `< q` vanishes and `δ = q + 1`). The signs at the block `2` are then flipped (`σ = -1`).
Both cases use `isRealJacquetFunctional_blockJacquet_flat` (`RealBlockFlatJacquet`).

### The case theorem `interlaced_AC`

Let `0 < k ≤ q ≤ p` and `s - t = |p - q|/2 + k`. Then
`RealLinkedJacquetFunctionalExists 4 [induced d, induced e]`. Proof: take `r = (p - q) mod 2`
and `m = p + 1 - r`, so that `r + m = p + 1`, `m ≥ q` and `m + q` is odd. Take `exists_flat_AC`
for this `m`, and `exists_tail_mult` with `B = q - k` and `j = -(m - k mod 2)`. Here
`|j| > q - k` and `j ≡ q + 1 + k`. The four exponent differences follow from the linking
equation by `natAbs_sub_cast`. Then apply `engine_AC`.

The module compiles with no errors or warnings.

## Provenance

Internal to the proof of `RealInterlacedInducedInducedLinkedJacquetFunctionalStatement`. The chain moves `u₂` to the front: first past `v₁` (tail multiplier),
then past `u₁` (generic multiplier). The binomial functional at the middle block (`u₁, v₁`) or,
failing that, the flat sign multiplier there followed by the binomial functional for `(v₁, v₂)`
gives the linked functional. The flat functional at the induction block `e` fixes the parity of
the final evaluation. The multipliers are the Library's (`RealBlockMultiplier`).
