# Proof of the finite binomial expansions for unipotent operators

This file proves the two auxiliary assertions stated in
`Langlands/LinearAlgebra/UnipotentBinomialStatement.lean`. They are used at the
end of the proof of the proposition in Renard, Appendix C.III, printed pages
279–280, PDF pages 285–286, in the French version dated 9 July 2026 (registered
source `renard-2026-representations-groupes-reductifs-padiques`). The source
gives no separate argument for these two facts. The Lean proof below is
self-contained over Mathlib. It does not use the vector-level result
`Langlands.IntegerLatticeExponentialPolynomial.zpow_apply_of_genEigen` or its
coefficient `binomCoeff`.

## Exported theorems

- `Langlands.complexBinomialCoefficientPolynomial :
  ComplexBinomialCoefficientPolynomialStatement`
- `Langlands.integerUnipotentBinomial : IntegerUnipotentBinomialStatement.{u}`
- `Langlands.renardCIIIUnipotentBinomial :
  RenardCIIIUnipotentBinomialStatement.{u}`, the pair of the two theorems
  above. Its type is exactly the published aggregate.
- `Langlands.truncatedBinomialSum_mul_one_add`, a helper lemma described below.

All of them use only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`. No hypothesis is added to the statements.

## Polynomial coefficients

Fix `j : ℕ` and `z : ℂ`. Mathlib's `Ring.choose_eq_smul`, for a field of
characteristic zero, writes `Ring.choose z j` as
`(j.factorial : ℂ)⁻¹ • (descPochhammer ℤ j).smeval z`. After `Polynomial.eval_smul`
moves the scalar out of the evaluation on the left, it remains to show
`(descPochhammer ℂ j).eval z = (descPochhammer ℤ j).smeval z`. The proof rewrites
`descPochhammer ℂ j` as the image of `descPochhammer ℤ j` under the ring
homomorphism `Int.castRingHom ℂ` (`descPochhammer_map`). By `Polynomial.eval_map`,
its evaluation at `z` is `eval₂ (Int.castRingHom ℂ) z (descPochhammer ℤ j)`. By
`Polynomial.eval₂_smulOneHom_eq_smeval`, `smeval` is `eval₂` along
`RingHom.smulOneHom : ℤ →+* ℂ`. The two ring homomorphisms out of `ℤ` agree
because that type of ring homomorphisms is a subsingleton. The argument holds
for every `j`, including `j = 0`, and for every complex `z`.

## The truncated Pascal rule

`truncatedBinomialSum_mul_one_add` works in any ring `A` with a compatible
complex scalar action. It takes `N : A` with `N ^ r = 0` and writes
`S(z) = ∑ j ∈ Finset.range r, Ring.choose z j • N ^ j`. It proves
`S(z) * (1 + N) = S(z + 1)` for every complex `z`. For `r = 0` both sides are
empty sums. For `r = s + 1` the proof distributes the product and pulls the
scalars through with `smul_mul_assoc`. It splits off the top term
`Ring.choose z s • N ^ (s + 1)` of `S(z) * N` with `Finset.sum_range_succ`; that
term vanishes by the hypothesis. It splits off the `j = 0` terms of `S(z)` and
`S(z + 1)` with `Finset.sum_range_succ'`. Pascal's rule `Ring.choose_succ_succ`,
`Ring.choose (z + 1) (k + 1) = Ring.choose z k + Ring.choose z (k + 1)`, together
with `Ring.choose_zero_right`, then matches the remaining terms, and `abel`
closes the goal.

## The all-integer expansion

For `integerUnipotentBinomial`, let `g` be a unit of `Module.End ℂ V` and put
`N = g - 1`, so that `g = 1 + N` and `N ^ r = 0`. The helper lemma gives
`S(z) * g = S(z + 1)` for all complex `z`. The proof shows that the endomorphism
underlying `g ^ n` is `S(n)` for every `n : ℤ`, by Mathlib's integer induction
`Int.induction_on`:

- `n = 0`: the left side is `1`. If `r = 0`, the hypothesis `N ^ 0 = 0` says
  `1 = 0` in `Module.End ℂ V`, and the empty sum is `0`. This case includes the
  zero space. If `r = s + 1`, then `S(0) = 1`, because `Ring.choose 0 0 = 1` and
  `Ring.choose 0 (k + 1) = 0` (`Ring.choose_zero_succ`).
- `n = k + 1` with `k ≥ 0`: `g ^ (k + 1) = g ^ k * g` (`zpow_add_one`), and
  `S(k) * g = S(k + 1)`.
- `n = -k - 1` with `k ≥ 0`: put `z = -k - 1`. The helper lemma gives
  `S(z) * g = S(-k)`, which equals `g ^ (-k)` by the induction hypothesis. Then
  `g ^ (-k - 1) = g ^ (-k) * g⁻¹` (`zpow_sub_one`) equals
  `S(z) * g * g⁻¹ = S(z)`, by `Units.mul_inv`.

Negative powers are therefore taken with the inverse in the actual unit group
`(Module.End ℂ V)ˣ`, as the statement requires. There is no hypothesis of finite
dimension, nontriviality, positive `r` or nonnegative `n`.
