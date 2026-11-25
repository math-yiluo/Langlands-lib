# The Langlands quotient of a Langlands-ordered real principal series (character blocks)

Lean module: `Langlands.Representation.Archimedean.RealCharacterLanglandsQuotient`.

This module proves
the case of character lists of `RealStandardLanglandsQuotientStatement` (L, module
`RealLargeLanglandsQuotientReduction`), the L input of the Library's
`realLargeLanglandsQuotientReduction`, conditionally on three statements stated in the Library
(see "The statement"). It extends the published `RealStrictCharacterLanglandsQuotient` (strictly
decreasing exponents) to Langlands-ordered character lists with ties. Its structure follows
`ComplexBlockLanglandsQuotient`.

Notation: `GL_n(ℝ)` is `Langlands.GeneralLinear n ℝ` and `O(n)` is `unitaryCompact ℝ n`. A
`RealBlock` is `.character d` (the character `sgn^ε |·|^t` of `ℝˣ`, rank `1`) or `.induced d`
(rank `2`); `realRank ds` is the total rank and `realBlockExponent x` the real part of the exponent
of `x` (`RealGenericParameterReduction`). `IsRealLanglandsOrdered ds` says that
`realBlockExponent` is non-increasing along `ds`. `RealStrictCharacterLanglandsQuotient.IsCharacterList ds`
says every block of `ds` is a character block. `realStandardModule n ds`, `realStandardRep`,
`realStandardLie`, `kFiniteFunctions` and `IsGKSubmodule` are the Library's. `realPositionCharacter ds`
and `realPositionExponent ds` are the characters and exponents at the positions
(`StandardModule`, `PrincipalSeriesGramFormula`). `IsSignedPower`, `largestProper`,
`IsProperGKStable`, `isGKStable_largestProper` and `le_largestProper` come from the Library's
`PartialJacquetIntegral` and `StrictPrincipalSeriesQuotient`. `dim`, `BlockOrdered`,
`TiedIrreducible`, `jacKernel` and `jac_eq_zero_of_proper` come from `RealBlockFunctional`,
`exists_jac_testVector_ne_zero` and `testVector_mem` from `RealBlockNonvanishing`, and
`realTiedIrreducible` from `RealTiedIrreducible`. Unprefixed names below are in the namespace
`Langlands.Archimedean.RealCharacterLanglandsQuotient`.

## The statement

`RealCharacterLanglandsQuotientStatement` assumes three statements:
`RealBlockChartIntegrableStatement` (proved as `realBlockChartIntegrable`),
`RealBlockParabolicIntegrationStatement` (proved as `realBlockParabolicIntegration`) and
`RealTemperedStandardIrreducibleStatement` (proved as `realTemperedStandardIrreducible`). Under these
assumptions it says the following.

For every `n` and every list `ds` of character blocks with `realRank ds = n` and
`IsRealLanglandsOrdered ds`, there is a submodule `R` of the `O(n)`-finite functions of
`realStandardModule n ds` that satisfies three conditions:

* `R` is a `(𝔤, K)`-submodule;
* `R ≠ ⊤`;
* `R` contains every `(𝔤, K)`-submodule `W ≠ ⊤`.

This is exactly the conclusion of `RealStandardLanglandsQuotientStatement` at such `ds`. The
statement is proved as `Langlands.Archimedean.realCharacterLanglandsQuotient`.

Provenance. The conclusion is that of the Library statement `RealStandardLanglandsQuotientStatement`
(Knapp 1994, Theorem 1(a), with Langlands' multiplicity-one theorem; see its Markdown), restricted
to lists of character blocks and made conditional on the three named statements. The restriction and
the hypotheses are derived; no additional literature statement is claimed.

## Proof

* `exists_blocks`: if `Re e_{l+1} ≤ Re e_l` for `l + 1 < n`, there is a block decomposition `ks`
  with `dim ks = n` and `BlockOrdered ks e`. The proof is by strong induction on `n`. For
  `n = m + 1`, let `a` be the least index with `Re e_j = Re e_m` for all `a ≤ j ≤ m` (`Nat.find`).
  The induction hypothesis at `a` gives `ks'`, and `ks = (m − a) :: ks'`. The block
  `a, …, m` is tied, the order before `a` is the hypothesis, and the gap at `a` follows from
  minimality: `Re e_{a−1} = Re e_a` would make `a − 1` admissible.
* `exponent_ord`: for a Langlands-ordered list of character blocks, the real parts of
  `realPositionExponent ds` are non-increasing on the positions `< realRank ds` (induction on the
  list, as `RealStrictCharacterLanglandsQuotient.isStrictlyDominant`).
* `isProperGKStable_largestProper_block`: let `ks` satisfy `BlockOrdered ks e`, and let `χ` be
  signed-power with signs `(−1)^{p_l}`. Assume `TiedIrreducible` and the two block statements. Then
  `largestProper (dim ks) χ`, the sum of all proper `(𝔤, K)`-stable subspaces, is proper and
  `(𝔤, K)`-stable. Every proper `W` lies in `jacKernel` (`jac_eq_zero_of_proper`), hence so does
  the sum (`iSup_le`). The test vector of `exists_jac_testVector_ne_zero` has `jac ≠ 0`, so it is
  not in the sum.
* `realCharacterLanglandsQuotient`: put `χ = realPositionCharacter ds`. It is signed-power with
  exponents `realPositionExponent ds` (`isSignedPower`), with signs from `exists_signs`.
  `exists_blocks` and `exponent_ord` give `ks` with `dim ks = realRank ds = n`; substituting `n`,
  `isProperGKStable_largestProper_block` applies, with `TiedIrreducible` from
  `realTiedIrreducible`. The rest is the argument of the published
  `realStrictCharacterLanglandsQuotient`:
  * `realStandardModule n ds = principalSeries ℝ n χ` (`realStandardModule_eq`);
  * `R` is the preimage of `largestProper n χ` in the `O(n)`-finite standard module;
  * `R` is a `(𝔤, K)`-submodule (induction on tensors for `realStandardLie`);
  * `R ≠ ⊤` because the test vector is not in `largestProper`;
  * every proper `(𝔤, K)`-submodule `W` maps to a proper `(𝔤, K)`-stable subspace of the principal
    series, which lies in `largestProper`.
