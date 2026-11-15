# The Langlands quotient of a strictly ordered complex standard module

Lean module: `Langlands.Representation.Archimedean.ComplexStrictLanglandsQuotient`.

Worker 140 wrote this module for Task 7063 (`f2d2e257-dd4b-4820-96ab-faa9c832ffb8`), the proof of
`ComplexStandardLanglandsQuotientStatement`. It is the complex counterpart of Worker 5220's modules
`StrictPrincipalSeriesQuotient` and `RealStrictCharacterLanglandsQuotient` for `GL_n(ℝ)`
(Task 6749), and follows their proofs.

The module proves the Langlands quotient statement for complex standard modules whose exponents
have strictly decreasing real parts: the `U(n)`-finite functions of the standard module have a
largest proper `(𝔤𝔩_n(ℂ), U(n))`-submodule. The statement is
`Langlands.Archimedean.ComplexStrictLanglandsQuotientStatement`, proved as
`Langlands.Archimedean.complexStrictLanglandsQuotient`. It is the case without ties of the
target `ComplexStandardLanglandsQuotientStatement` (whose Langlands order allows equal real parts).

Notation: `GL_n(ℂ)` is `Langlands.GeneralLinear n ℂ`, `U(n)` is `unitaryCompact ℂ n`.
`ComplexCharacterData`, `complexPositionCharacter`, `complexStandardModule`, `complexStandardRep`,
`complexStandardLie`, `kFiniteFunctions`, `IsGKSubmodule`, `principalSeriesRep_apply_coe`,
`principalSeriesLie_one_tmul_apply_coe`, `rightDerivative_add` and `rightDerivative_smul` are the
Library's. `IsPhasePower` and `IsStrictlyDominant` come from `ComplexPartialJacquet`; `jacquet`
from `ComplexJacquetDual`; `jacquetKernel` and `jacquet_eq_zero_of_proper` from
`ComplexJacquetKernel`; `exists_jacquet_ne_zero` from `ComplexJacquetNonvanishing`;
`phaseUnit`, `complexPositionExponent` and `complexPositionCharacter_eq_phaseUnit_mul` from
`ComplexGramFormula`. Declarations without a prefix are in the namespace
`Langlands.Archimedean.ComplexStrictLanglandsQuotient`.

## The statement

`ComplexStrictLanglandsQuotientStatement`: for every `n` and every list `ds` of `n` complex
characters `z ↦ (z/|z|)^{l_i} |z|^{2 t_i}` with `Re t_j < Re t_i` whenever `d_i` precedes `d_j` in
`ds` (`List.Pairwise`), there is a submodule `R` of the `U(n)`-finite functions of
`complexStandardModule n ds` that is a `(𝔤, K)`-submodule for
`(complexStandardRep n ds, complexStandardLie n ds)`, is not everything, and contains every
`(𝔤, K)`-submodule that is not everything.

Provenance. Badulescu–Renard 2010, Theorem 3.3 (i), and Knapp 1994, Theorem 4 (a) (cited by the
target statement) give the existence of the Langlands quotient for all Langlands-ordered lists;
this is its special case with strict inequalities, which the module proves by the
Langlands-lemma argument (Jacquet integral), not by quoting the sources.

## The largest proper submodule of a strictly dominant principal series

* `IsGKStable n χ W`: `W` lies in the `U(n)`-finite principal series of `χ` and is stable under
  right translation by `U(n)` and all right derivatives. `IsProperGKStable n χ W` adds that some
  `U(n)`-finite function of the principal series is not in `W`.
* `largestProper n χ` is the supremum of all proper `(𝔤, K)`-stable subspaces. It is contained in
  the `U(n)`-finite principal series (`largestProper_le`) and is `(𝔤, K)`-stable
  (`isGKStable_largestProper`, by `Submodule.iSup_induction`, with `rightDerivative_add` and
  `rightDerivative_zero`).
* `isProperGKStable_largestProper`: for strictly dominant phase-power `χ` with
  `χ_l(u) = u^{p_l}` on the unit circle, `largestProper n χ` lies in the kernel of the Jacquet
  integral (every proper `(𝔤, K)`-stable subspace does, `jacquet_eq_zero_of_proper`, and the
  kernel is a subspace), and it is proper: the Jacquet integral is nonzero on some `U(n)`-finite
  `f` (`exists_jacquet_ne_zero`), and such `f` is not in the kernel.

## The characters of a list of complex characters

* `complexPositionWeight ds l` is the weight of the `l`-th character of `ds` (`0` past the end).
* `complexPositionCharacter_one`: every position character is `1` at `1`.
* `complexPositionCharacter_phase`: on `z/|z|` the `l`-th position character is
  `(z/|z|)^{weight}` (from `ComplexCharacterData.character_eq` and `|z/|z|| = 1`).
* `isPhasePower ds`: the position characters are phase powers with exponents
  `complexPositionExponent ds` (`complexPositionCharacter_eq_phaseUnit_mul`).
* `IsStrictlyOrdered ds` (strictly decreasing real parts of the exponents) gives
  `IsStrictlyDominant (complexPositionExponent ds) (ds.length − 1)` (`isStrictlyDominant`, by
  induction on `ds`).

## Proof of the statement

`complexStrictLanglandsQuotient`. Put `χ = complexPositionCharacter ds`; `complexStandardModule n ds`
is by definition `principalSeries ℂ n χ`, so its `U(n)`-finite functions `S` are those of the
principal series. Let `R = (largestProper n χ) ∩ S`, as a submodule of `S`.

* `R` is a `(𝔤, K)`-submodule: `complexStandardRep n ds κ` is right translation by `κ`
  (`principalSeriesRep_apply_coe`), and `complexStandardLie n ds (c ⊗ X) = c · R(X)`
  (`principalSeriesLie_one_tmul_apply_coe`, with induction on tensors).
* `R ≠ ⊤`: the function `f₀ ∉ largestProper n χ` from `isProperGKStable_largestProper`.
* Every `(𝔤, K)`-submodule `W ≠ ⊤` of `S` maps to a proper `(𝔤, K)`-stable subspace of the
  principal series (an element of `S` outside `W` witnesses properness), so `W ≤ R` by
  `le_largestProper`.
