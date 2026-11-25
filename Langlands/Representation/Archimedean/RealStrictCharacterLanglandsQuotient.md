# The Langlands quotient of a strictly ordered real principal series

Lean module: `Langlands.Representation.Archimedean.RealStrictCharacterLanglandsQuotient`.

This module proves the Langlands-quotient statement `RealStandardLanglandsQuotientStatement`
(Library module `RealLargeLanglandsQuotientReduction`) in one special case. The blocks must all
be characters of `GL_1(ℝ)`, and their exponents must have strictly decreasing real parts. The
statement is
`Langlands.Archimedean.RealStrictCharacterLanglandsQuotient.RealStrictCharacterLanglandsQuotientStatement`,
proved as
`Langlands.Archimedean.RealStrictCharacterLanglandsQuotient.realStrictCharacterLanglandsQuotient`.

It is the strictly ordered principal-series case of the statement L,
`RealStandardLanglandsQuotientStatement`. The general L
also allows equal exponents (ties) and induced `GL_2` blocks, and is not proved here.

Declarations without a prefix are in the namespace
`Langlands.Archimedean.RealStrictCharacterLanglandsQuotient`.

## The statement

`RealStrictCharacterLanglandsQuotientStatement`. Let `n : ℕ` and `ds : List RealBlock` satisfy:

* `realRank ds = n`;
* every block is a character: `IsCharacterList ds`, that is, `∀ b ∈ ds, ∃ c, b = .character c`;
* the real parts of the exponents strictly decrease: `IsStrictlyOrdered ds`, that is,
  `ds.Pairwise fun x y => realBlockExponent y < realBlockExponent x`.

Then there is a submodule `R` of `kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)`
with three properties:

* `R` is a `(𝔤, K)`-submodule (`IsGKSubmodule (realStandardRep n ds) (realStandardLie n ds) R`);
* `R ≠ ⊤`;
* every `(𝔤, K)`-submodule `W ≠ ⊤` satisfies `W ≤ R`.

This is the conclusion of `RealStandardLanglandsQuotientStatement`, word for word. The only
change is that the hypothesis `IsRealLanglandsOrdered ds` (non-strict) is replaced by the two
hypotheses above.

Provenance. Derived from the Library statement `RealStandardLanglandsQuotientStatement`, which
cites Knapp 1994, Theorem 1(a) and Langlands' multiplicity-one theorem, by restricting to
character blocks in strict order. The proof is the Langlands-lemma argument, carried out by
induction in stages along the maximal parabolic subgroups `P_{n−1,1}`.

## Proof

1. **The standard module is the principal series** (`realStandardModule_eq`). For a character
   list, `realInducedBlockAt ds p = none` for every `p` (`realInducedBlockAt_eq_none`). So the
   Fourier conditions in `realStandardModule` are vacuous.
2. **Position characters.** The position characters `realPositionCharacter ds` form a signed power
   with exponents `realPositionExponent ds` (`isSignedPower`). This uses
   `GramFormula.realPositionCharacter_eq_signUnit_mul`, `realPositionCharacter_one`, and the fact
   that each value at `−1` is `±1` (`realPositionCharacter_neg_one`). In particular signs `p`
   with `χ_l(−1) = (−1)^{p_l}` exist (`exists_signs`). Strict order of the blocks gives
   `IsStrictlyDominant (realPositionExponent ds) (n − 1)` (`isStrictlyDominant`), by induction on
   the list.
3. **The largest proper subspace.** `StrictPrincipalSeriesQuotient.isProperGKStable_largestProper`
   gives a proper `(𝔤, K)`-stable subspace `largestProper` of the `O(n)`-finite principal series
   that contains every proper `(𝔤, K)`-stable subspace.
4. **Translation to submodules of the subtype.** Take `R` to be the preimage of `largestProper`
   under the inclusion of `kFiniteFunctions (realStandardModule n ds) _`.
   * `realStandardRep` acts by right translation (`realStandardRep_apply_coe`), and
     `realStandardLie (1 ⊗ X)` acts by the right derivative `R(X)`
     (`realStandardLie_one_tmul_apply_coe`). The full Lie action is `ℂ`-linear in `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)`
     (`TensorProduct.inductionOn`). So `R` is a `(𝔤, K)`-submodule.
   * `R ≠ ⊤`, because some `f₀` of the principal series is not in `largestProper`.
   * Let `W ≠ ⊤` be a `(𝔤, K)`-submodule. Its image under the inclusion is a proper
     `(𝔤, K)`-stable subspace: an element of the subtype outside `W` gives a function outside the
     image. Hence the image lies in `largestProper`, so `W ≤ R`.

## Supporting modules

* `ParabolicChartBound`: growth bounds along `J(x,1)`.
* `PartialJacquetIntegral`: the partial Jacquet integral `T`.
* `JacquetLimit`: the limit argument.
* `JacquetDual`: the Jacquet integral `Λ_n` in stages and the dual induction `D(n)`.
* `TranslateFinite`: polynomial functions on `O(n)` are `O(n)`-finite.
* `JacquetKernel`: proper submodules lie in `ker Λ_n`.
* `JacquetNonvanishing`: `Λ_n ≠ 0`.
* `StrictPrincipalSeriesQuotient`: the largest proper submodule.

These modules rest on the Library modules `MaximalParabolicIntegration`,
`OrthogonalLastRowIntegral`, `KIntegralInvariance`, `PrincipalSeriesExtension`,
`PrincipalSeriesAnnihilator`, `PrincipalSeriesMatrixCoefficientAnalytic`,
`PrincipalSeriesGramFormula`, `OrthogonalFinitePolynomial` and `RealPrincipalSeriesDualityProof`.
