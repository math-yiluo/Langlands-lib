# Pole orders at `s = 0` of supercuspidal pairs of equal rank

This module computes the order of the pole at `s = 0` of `L(s, π × σ)` for an
irreducible supercuspidal `π` and an irreducible `σ` of Whittaker type, both
representations of `GL_(r+1)(F)`. The order is `1` if `π` is equivalent to the
smooth contragredient `σ̃` and `0` otherwise. The result is conditional. It
takes the Library's unproved `SupercuspidalEqualRankLFactorStatement`, which
states Proposition (8.1)(ii) of JPSS 1983, as an explicit hypothesis.

## Provenance

Derived. Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg convolutions*,
Amer. J. Math. 105 (1983), Proposition (8.1)(ii), printed page 443: if `π` is
irreducible supercuspidal and `σ` is irreducible of Whittaker type of the same
rank, then `L(s, π × σ) = ∏ (1 - a q^(-s))^(-1)`, the product taken over all
`a = q^(-u)` such that `π ⊗ α^(-u) ≃ σ̃`. The printed condition reads
`π ⊗ α^(-u) ≃ σ`, a misprint; the Library statement uses the corrected
condition with `σ̃` (see "Interpretation" in the Markdown of
`TemperedLFactorStatement`). At `s = 0` the factor `1 - a q^(-s)` vanishes
exactly when `a = 1`. The value `a = 1` occurs exactly when `π ≃ σ̃`, because
`α^(-u)` is trivial when `q^(-u) = 1`. Henniart 2002, §4, uses this pole count
at `s = 0`. The module records this consequence of (8.1)(ii) in the Library's
terms.

## Contents

- `contragredientIndicator F π σ`: for representations `π` and `σ` of
  `GL_(r+1)(F)`, the natural number `1` if `π` is equivalent to the smooth
  contragredient `σ̃` (`smoothContragredient σ`), and `0` otherwise. The
  equivalence condition is a proposition, so the `if` uses classical
  decidability (`open Classical in`). This is an internal definition: it names
  the indicator `[π ≃ σ̃]` that (8.1)(ii) gives as the pole order at `s = 0`.
- `normalizedAbs_cpow_eq_one`: if `q^(-u) = 1` in `ℂ`, then
  `|x|^(-u) = 1` for every nonzero `x ∈ F`. Here `q` is the residue
  cardinality and `|x|` the normalized absolute value. The proof writes
  `|x| = q^k` with `k ∈ ℤ` (`PadicField.TopologicalData.normalizedAbs_of_ne_zero`)
  and uses `(q^k)^(-u) = (q^(-u))^k`. This identity of complex powers holds
  because `q` is a positive real number, so its argument is `0`.
- `one_mem_iff_of_supercuspidalTwistSet`: let `A` be a finite set of complex
  numbers described as in `SupercuspidalEqualRankLFactorStatement`. That is,
  `a ∈ A` exactly when `a = q^(-u)` for some `u` for which some character `χ`
  of `F^×` with `χ(x) = |x|^(-u)` makes `π ⊗ (χ ∘ det)` equivalent to `σ̃`.
  Then `1 ∈ A` exactly when `π` is equivalent to `σ̃`. In one direction,
  `q^(-u) = 1` forces `χ = 1` by the previous lemma, and the twist by the
  trivial character is `π` (`Langlands.twist_one`, used through `simp`). In
  the other direction, take `u = 0` and `χ = 1`.
- `lPolynomialPoleOrderAtZero_of_supercuspidalEqualRank`: assume
  `SupercuspidalEqualRankLFactorStatement`. Let `π` be irreducible and
  supercuspidal and `σ` irreducible and of Whittaker type for the standard
  character `standardCharacter ψ r`, both of `GL_(r+1)(F)`. Let `P` be any
  polynomial with `IsPadicPairLPolynomial F ψ ν.val π σ P`. Then
  `lPolynomialPoleOrderAtZero P = contragredientIndicator F π σ`, that is,
  `1` if `π` is equivalent to `σ̃` and `0` otherwise. The hypothesis gives `A` with `IsPadicPairLPolynomial` for
  `∏_(a ∈ A) (1 - a X)`. Uniqueness of the L-polynomial
  (`IsPadicPairLPolynomial.unique`) identifies `P` with this product. The pole
  order of the product is computed by
  `lPolynomialPoleOrderAtZero_prod_one_sub_C_mul_X` from
  `PoleOrderAtZeroArithmetic` as `if 1 ∈ A then 1 else 0`, and the previous
  lemma identifies the condition `1 ∈ A` with the condition in
  `contragredientIndicator`.
